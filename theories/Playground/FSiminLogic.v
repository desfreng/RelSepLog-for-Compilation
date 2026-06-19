From RSL Require Import RLogic Prelude.

From iris.bi Require Import bi fixpoint_mono.
From iris.proofmode Require Import proofmode.

From RSL Require Import Playground.toto.

Definition curry5 {A B C D E F: Type} (f : A * B * C * D * E -> F) :=
  fun a b c d e => f (a, b, c, d, e).

Definition uncurry5 {A B C D E F: Type} (f : A -> B -> C -> D -> E -> F) :=
  fun '(a, b, c, d, e) => f a b c d e.

Section FSimDef.
  Context {Λₜ Λₛ: lang}.
  Context (J I: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Context (S : state Λₜ -> state Λₛ -> rlogic).

  Abbreviation post := (value Λₜ -> value Λₛ -> rlogic).
  Abbreviation sim_rel := (post -> state Λₜ -> J -> I -> state Λₛ -> rlogic).

  Definition both_final (ϕ: post) (t: state Λₜ) (s: state Λₛ) : rlogic :=
    ∃ vₜ vₛ, <affine>⌜is_final t = Some vₜ⌝ ∗ <affine>⌜is_final s = Some vₛ⌝ ∗ ϕ vₜ vₛ.

  Definition fsim_body (gfp: sim_rel) (lfp: sim_rel) : sim_rel :=
    fun ϕ t j i s =>
    (S t s -∗
     (both_final ϕ t s           (* Related *))
     ∨
     (<affine>⌜stuck Pₛ s⌝       (* Source Stuck *))
     ∨
     (∀ s' i',                   (* Source Steps *)
        <affine>⌜Pₛ ⊨ s ->> s'⌝ ∗ S t s' ∗ lfp ϕ t j i' s')
     ∨
     (                           (* Target Steps *)
       <affine>⌜can_progress Pₜ t⌝ ∗
       (∀ t',
          <affine>⌜Pₜ ⊨ t ->> t'⌝ -∗
          S t' s ∗ ∃ j', lfp ϕ t' j' i s))
     ∨
     (∀ j' i',                   (* Progress *)
        <affine>⌜j' ⊏ j⌝ ∗
        <affine>⌜i' ⊏ i⌝ ∗
        gfp ϕ t j' i' s)
    )%I.

  Lemma fsim_body_mono lfp1 lfp2 gfp1 gfp2:
    ⊢ □ (∀ ϕ t j i s,
           lfp1 ϕ t j i s -∗ lfp2 ϕ t j i s)
    → □ (∀ ϕ t j i s,
           gfp1 ϕ t j i s -∗ gfp2 ϕ t j i s)
    → ∀ ϕ t j i s,
        fsim_body gfp1 lfp1 ϕ t j i s -∗
        fsim_body gfp2 lfp2 ϕ t j i s.
  Proof using Type.
    iIntros "#Hlfp #Hgfp" (ϕ t j i s) "Hsim".
    unfold fsim_body.
    iIntros "Hstate".
    iDestruct ("Hsim" with "Hstate")
      as "[Hfin | [Hstuck | [Hs | [(Hprog & Ht) | Hprog]]]]".
    - do 0 iRight. now iLeft.
    - do 1 iRight. now iLeft.
    - do 2 iRight. iLeft.
      iIntros "%s' %i''".
      iDestruct ("Hs" $! s' i'') as "(Hstep & Hstate & Hsim)".
      iFrame.
      iApply ("Hlfp" with "Hsim").
    - do 3 iRight. iLeft. iFrame.
      iIntros "%t' Hstep".
      iDestruct ("Ht" $! t' with "Hstep") as "(Hstate & [%j' Hsim])".
      iFrame. iExists j'.
      iApply ("Hlfp" with "Hsim").
    - do 4 iRight.
      iIntros "%j'' %i''".
      iDestruct ("Hprog" $! j'' i'') as "(Hj' & Hi' & Hsim)".
      iFrame.
      iApply ("Hgfp" with "Hsim").
  Qed.

  Lemma strong_fsim_body_mono lfp1 lfp2 gfp1 gfp2:
    ⊢ □ (∀ ϕ Ψ t j j' i i' s,
           □ (∀ t s, ϕ t s -∗ Ψ t s) -∗
           <affine>⌜j ⊑ j'⌝ -∗
           <affine>⌜i ⊑ i'⌝ -∗
           lfp1 ϕ t j i s -∗ lfp2 Ψ t j' i' s)
    → □ (∀ ϕ Ψ t j j' i i' s,
           □ (∀ t s, ϕ t s -∗ Ψ t s) -∗
           <affine>⌜j ⊑ j'⌝ -∗
           <affine>⌜i ⊑ i'⌝ -∗
           gfp1 ϕ t j i s -∗ gfp2 Ψ t j' i' s)
    → ∀ ϕ Ψ t j j' i i' s,
        □ (∀ t s, ϕ t s -∗ Ψ t s) -∗
        <affine>⌜j ⊑ j'⌝ -∗
        <affine>⌜i ⊑ i'⌝ -∗
        fsim_body gfp1 lfp1 ϕ t j i s -∗
        fsim_body gfp2 lfp2 Ψ t j' i' s.
  Proof using Type.
    iIntros "#Hlfp #Hgfp" (ϕ Ψ t j j' i i' s) "#Hpost %Hj %Hi Hsim".
    unfold fsim_body.
    iIntros "Hstate".
    iDestruct ("Hsim" with "Hstate")
      as "[Hfin | [Hstuck | [Hs | [(Hprog & Ht) | Hprog]]]]".
    - do 0 iRight. iLeft.
      unfold both_final.
      iDestruct "Hfin" as "(%vt & %vs & Ht & Hs & Hfin)".
      iExists vt, vs. iFrame.
      iApply ("Hpost" with "Hfin").
    - do 1 iRight. now iLeft.
    - do 2 iRight. iLeft.
      iIntros "%s' %i''".
      iDestruct ("Hs" $! s' i'') as "(Hstep & Hstate & Hsim)".
      iFrame.
      iApply ("Hlfp" with "Hpost [] [] Hsim").
      + now iPureIntro.
      + now iPureIntro.
    - do 3 iRight. iLeft. iFrame.
      iIntros "%t' Hstep".
      iDestruct ("Ht" $! t' with "Hstep") as "(Hstate & [%j'' Hsim])".
      iFrame. iExists j''.
      iApply ("Hlfp" with "Hpost [] [] Hsim").
      + now iPureIntro.
      + now iPureIntro.
    - do 4 iRight.
      iIntros "%j'' %i''".
      iDestruct ("Hprog" $! j'' i'') as "(%Hj' & %Hi' & Hsim)".
      iSplitR.
      { iPureIntro. eapply lt_from_lt_le; eassumption. }
      iSplitR.
      { iPureIntro. eapply lt_from_lt_le; eassumption. }
      iApply ("Hgfp" with "Hpost [] [] Hsim").
      + now iPureIntro.
      + now iPureIntro.
  Qed.

  Instance fsim_body_proper:
    Proper (
        ((eq ==> eq ==> (⊢)) ==> eq ==> (⊑) ==> (⊑) ==> eq ==> (⊢)) ==>
        ((eq ==> eq ==> (⊢)) ==> eq ==> (⊑) ==> (⊑) ==> eq ==> (⊢)) ==>
        ((eq ==> eq ==> (⊢)) ==> eq ==> (⊑) ==> (⊑) ==> eq ==> (⊢))
      ) fsim_body.
  Proof using Type.
    intros gfp1 gfp2 Hgfp lfp1 lfp2 Hlfp.
    intros ϕ ψ Hpost t ? <- j j' Hj i i' Hi s ? <-.
    iIntros "Hsim". unfold fsim_body.
    iIntros "Hstate".
    iDestruct ("Hsim" with "Hstate")
      as "[Hfin | [Hstuck | [Hs | [(Hprog & Ht) | Hprog]]]]".
    - do 0 iRight. iLeft.
      unfold both_final.
      iDestruct "Hfin" as "(%vt & %vs & Ht & Hs & Hfin)".
      iExists vt, vs. iFrame.
      now iApply (Hpost with "Hfin").
    - do 1 iRight. now iLeft.
    - do 2 iRight. iLeft.
      iIntros "%s' %i''".
      iDestruct ("Hs" $! s' i'') as "(Hstep & Hstate & Hsim)".
      iFrame.
      now iApply (Hlfp with "Hsim").
    - do 3 iRight. iLeft. iFrame.
      iIntros "%t' Hstep".
      iDestruct ("Ht" $! t' with "Hstep") as "(Hstate & [%j'' Hsim])".
      iFrame. iExists j''.
      now iApply (Hlfp with "Hsim").
    - do 4 iRight.
      iIntros "%j'' %i''".
      iDestruct ("Hprog" $! j'' i'') as "(%Hj' & %Hi' & Hsim)".
      iSplitR.
      { iPureIntro. eapply lt_from_lt_le; eassumption. }
      iSplitR.
      { iPureIntro. eapply lt_from_lt_le; eassumption. }
      now iApply (Hgfp with "Hsim").
  Qed.

  Local Instance fsim_body_bimono gfp :
    BiMonoPred (λ lfp, uncurry5 (fsim_body gfp (curry5 lfp))).
  Proof using Type.
    constructor.
    intros lfp1 lfp2. iIntros "#H" (x).
    destruct x as ((((ϕ & t) & j) & i) & s); simpl.
    iApply (fsim_body_mono with "[] []"); iModIntro; clear.
    { iIntros (ϕ t j i s). iApply "H". }
    iIntros (ϕ t j i s) "$".
  Qed.

  Definition fsim_lfp_def (gfp: sim_rel) : sim_rel :=
    curry5 (bi_least_fixpoint (fun lfp => uncurry5 (fsim_body gfp (curry5 lfp)))).

  Lemma fsim_lfp_def_mono gfp gfp' ϕ t j i s :
    □ (∀ ϕ t j i s, gfp ϕ t j i s -∗ gfp' ϕ t j i s) -∗
    fsim_lfp_def gfp ϕ t j i s -∗ fsim_lfp_def gfp' ϕ t j i s.
  Proof using Type.
    iIntros "#H". unfold fsim_lfp_def, curry5.
    iIntros "Hsim".
    iApply (least_fixpoint_iter with "[] Hsim").
    iModIntro. clear ϕ t j i s.
    iIntros ([[[[ϕ t] j] i] s]).
    rewrite least_fixpoint_unfold.
    unfold uncurry5.
    iApply (fsim_body_mono with "[] []"); clear.
    - iModIntro. iIntros (ϕ t j i s ) "$".
    - iModIntro. iIntros (ϕ t j i s ). iApply "H".
  Qed.

  Lemma fsim_lfp_def_unfold gfp ϕ t j i s :
    fsim_lfp_def gfp ϕ t j i s ≡ fsim_body gfp (fsim_lfp_def gfp) ϕ t j i s.
  Proof using Type.
    unfold fsim_lfp_def at 1.
    unfold curry5 at 1.
    rewrite least_fixpoint_unfold.
    unfold uncurry5 at 1.
    reflexivity.
  Qed.

  Instance fsim_gfp_def_mono :
    BiMonoPred (fun gfp => uncurry5 (fsim_lfp_def (curry5 gfp))).
  Proof using Type.
    constructor.
    intros gfp1 gfp2. iIntros "#H" (x).
    destruct x as ((((ϕ & t) & j) & i) & s); simpl.
    iApply (fsim_lfp_def_mono).
    iModIntro; clear.
    { iIntros (ϕ t j i s). iApply "H". }
  Qed.

  Definition fsim_gfp_def : sim_rel  :=
    curry5 (bi_greatest_fixpoint (fun gfp => uncurry5 (fsim_lfp_def (curry5 gfp)))).

  Lemma fsim_gfp_def_unfold ϕ t j i s :
    fsim_gfp_def ϕ t j i s ≡ fsim_lfp_def fsim_gfp_def ϕ t j i s.
  Proof using Type.
    unfold fsim_gfp_def at 1.
    unfold curry5 at 1.
    rewrite greatest_fixpoint_unfold.
    unfold uncurry5 at 1.
    reflexivity.
  Qed.

  Lemma fsim_gfp_def_fixpoint ϕ t j i s:
    fsim_gfp_def ϕ t j i s ≡ fsim_body fsim_gfp_def fsim_gfp_def ϕ t j i s.
  Proof using Type.
    rewrite fsim_gfp_def_unfold fsim_lfp_def_unfold.
    iSplit.
    - iIntros "H". iApply (fsim_body_mono with "[] [] H"); auto.
      iIntros "!>" (? ? ? ? ?) "H".
      now iApply (fsim_gfp_def_unfold).
    - iIntros "H". iApply (fsim_body_mono with "[] [] H"); auto.
      iIntros "!>" (? ? ? ? ?) "H".
      now iApply (fsim_gfp_def_unfold).
  Qed.
End FSimDef.
