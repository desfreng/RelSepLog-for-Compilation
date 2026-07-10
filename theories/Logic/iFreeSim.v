From RSL Require Import Prelude.

From RSL.Commons Require Export WfRel Language.
From RSL.Logic Require Import Fixpoints.

From iris.proofmode Require Export proofmode.

Class SimInv (PROP : bi) (Λₜ Λₛ : lang) :=
  {
    sim_inv : state Λₜ -> state Λₛ -> PROP;
  }.

Section FSimDef.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP}.
  Context {Λₜ Λₛ: lang}.
  Context (J I: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).
  Context {sinv: SimInv PROP Λₜ Λₛ}.

  Set Default Proof Using "Type*".

  Abbreviation post := (value Λₜ -> value Λₛ -> PROP).
  Abbreviation sim_rel := (post -> state Λₜ -> J -> I -> state Λₛ -> PROP).

  Definition both_final (ϕ: post) (t: state Λₜ) (s: state Λₛ) : PROP :=
    ∃ vt vs mt ms,
      ⌜is_final t = Some (vt, mt)⌝ ∗
      ⌜is_final s = Some (vs, ms)⌝ ∗
      ϕ vt vs.

  Local Definition fsim_body (gfp: sim_rel) (lfp: sim_rel) : sim_rel :=
    fun ϕ t j i s =>
      (sim_inv t s ==∗
       (                          (* Related *)
         both_final ϕ t s
       ) ∨ (                       (* Source Stuck *)
         ⌜stuck Pₛ s⌝
       ) ∨ (                       (* Source Steps *)
         ∃ s' i',
           ⌜Pₛ ⊨ s ->> s'⌝ ∗ sim_inv t s' ∗ lfp ϕ t j i' s'
       ) ∨ (                       (* Target Steps *)
         ⌜can_progress Pₜ t⌝ ∗
         (∀ t',
            ⌜Pₜ ⊨ t ->> t'⌝ ==∗
            sim_inv t' s ∗ ∃ j', lfp ϕ t' j' i s)
       ) ∨ (                       (* Progress *)
         ∃ j' i',
           ⌜j' ⊏ j⌝ ∗
           ⌜i' ⊏ i⌝ ∗
           gfp ϕ t j' i' s
       )
      )%I.

  Local Lemma fsim_body_mono gfp1 gfp2 lfp1 lfp2:
    ⊢ □ (∀ ϕ t j i s, gfp1 ϕ t j i s -∗ gfp2 ϕ t j i s) →
      □ (∀ ϕ t j i s, lfp1 ϕ t j i s -∗ lfp2 ϕ t j i s) →
      ∀ ϕ t j i s,
        fsim_body gfp1 lfp1 ϕ t j i s -∗
        fsim_body gfp2 lfp2 ϕ t j i s.
  Proof.
    iIntros "#Hgfp #Hlfp" (ϕ t j i s) "Hsim Hin".
    iMod ("Hsim" with "Hin") as "Hsim".
    iDestruct ("Hsim")
      as "[Hfin | [Hstuck | [Hs | [(Hprog & Ht) | Hprog]]]]".
    - do 0 iRight. now iLeft.
    - do 1 iRight. now iLeft.
    - do 2 iRight. iLeft.
      iDestruct ("Hs") as (s' i') "(Hstep & Hstate & Hsim)".
      iExists s', i'. iFrame.
      iApply ("Hlfp" with "Hsim").
    - do 3 iRight. iLeft. iFrame.
      iModIntro. iIntros "%t' Hstep".
      iMod ("Ht" with "Hstep") as "(Hstate & [%j' Hsim])".
      iFrame. iExists j'.
      iApply ("Hlfp" with "Hsim").
    - do 4 iRight.
      iDestruct ("Hprog") as (j' i') "(Hj' & Hi' & Hsim)".
      iExists j', i'. iFrame.
      iApply ("Hgfp" with "Hsim").
  Qed.

  Local Lemma fsim_body_mono_strong gfp1 gfp2 lfp1 lfp2:
    ⊢ □ (∀ ϕ ϕ' t j j' i i' s,
           □ (∀ vt vs, ϕ vt vs -∗ ϕ' vt vs) -∗
           ⌜j ⊑ j'⌝ -∗
           ⌜i ⊑ i'⌝ -∗
           gfp1 ϕ t j i s -∗ gfp2 ϕ' t j' i' s) -∗
      □ (∀ ϕ ϕ' t j j' i i' s,
           □ (∀ vt vs, ϕ vt vs -∗ ϕ' vt vs) -∗
           ⌜j ⊑ j'⌝ -∗
           ⌜i ⊑ i'⌝ -∗
           lfp1 ϕ t j i s -∗ lfp2 ϕ' t j' i' s) -∗
      ∀ ϕ ϕ' t j j' i i' s,
      □ (∀ vt vs, ϕ vt vs -∗ ϕ' vt vs) -∗
      ⌜j ⊑ j'⌝ -∗
      ⌜i ⊑ i'⌝ -∗
      fsim_body gfp1 lfp1 ϕ t j i s -∗
      fsim_body gfp2 lfp2 ϕ' t j' i' s.
  Proof.
    iIntros "#Hgfp #Hlfp" (ϕ ϕ' t j j' i i' s) "#Hpost %Hj %Hi Hsim Hin".
    iMod ("Hsim" with "Hin") as "Hsim".
    iDestruct ("Hsim") as "[Hfin | [Hstuck | [Hs | [(Hprog & Ht) | Hprog]]]]".
    - do 0 iRight. iLeft.
      iDestruct ("Hfin") as "(%vt & %vs & %mt & %ms & Ht & Hs & Hfin)".
      iExists vt, vs, mt, ms. iFrame.
      by iApply ("Hpost" with "Hfin").
    - do 1 iRight. now iLeft.
    - do 2 iRight. iLeft.
      iDestruct ("Hs") as (s' i'') "(Hstep & Hstate & Hsim)".
      iFrame. iExists i''.
      iApply ("Hlfp" with "Hpost [] [] Hsim"); by iPureIntro.
    - do 3 iRight. iLeft. iFrame. iModIntro.
      iIntros "%t' Hstep".
      iMod ("Ht" with "Hstep") as "(Hstate & [%j'' Hsim])".
      iFrame. iExists j''.
      iApply ("Hlfp" with "Hpost [] [] Hsim"); by iPureIntro.
    - do 4 iRight.
      iDestruct ("Hprog") as (j'' i'') "(%Hj' & %Hi' & Hsim)".
      destruct Hj as [Hj | <-]; destruct Hi as [Hi| <-];
        iExists _, _; (iSplitR; [by iPureIntro|]); (iSplitR; [by iPureIntro|]);
        iApply ("Hgfp" with "Hpost [] [] Hsim"); iPureIntro;
        (left; assumption) || (right; reflexivity).
  Qed.

  Local Instance fsim_body_bimono gfp :
    BiMonoPred (λ lfp, uncurry5 (fsim_body gfp (curry5 lfp))).
  Proof.
    constructor.
    intros lfp1 lfp2. iIntros "#H" (x).
    destruct x as ((((ϕ & t) & j) & i) & s); simpl.
    iApply (fsim_body_mono with "[] []"); clear.
    - iIntros "!>" (ϕ t j i s) "$".
    - iIntros "!>" (ϕ t j i s). iApply "H".
  Qed.

  (** * Free Simulation Least-Fixpoint closed *)

  Definition fsim_lfp_def (gfp: sim_rel) : sim_rel :=
    curry5 (bi_least_fixpoint (fun lfp => uncurry5 (fsim_body gfp (curry5 lfp)))).

  Local Definition fsim_lfp_aux : seal fsim_lfp_def.
  Proof. by eexists. Qed.
  Definition fsim_lfp := unseal fsim_lfp_aux.
  Local Lemma fsim_lfp_eq : fsim_lfp = fsim_lfp_def.
  Proof. exact: seal_eq. Qed.

  Local Lemma fsim_lfp_unfold gfp ϕ t j i s :
    fsim_lfp gfp ϕ t j i s ≡ fsim_body gfp (fsim_lfp gfp) ϕ t j i s.
  Proof.
    rewrite fsim_lfp_eq.
    unfold fsim_lfp_def at 1.
    unfold curry5 at 1.
    rewrite least_fixpoint_unfold.
    unfold uncurry5 at 1.
    reflexivity.
  Qed.

  Lemma fsim_related G ϕ t j i s :
    ∀ vt vs mt ms,
    is_final t = Some (vt, mt) ->
    is_final s = Some (vs, ms) ->
    ⊢ (sim_inv t s ==∗ ϕ vt vs) -∗
      fsim_lfp G ϕ t j i s.
  Proof.
    iIntros (vt vs mt ms Ht Hs) "HΦ".
    rewrite fsim_lfp_unfold.
    iIntros "Hin".
    do 0 iRight. iLeft.
    iSpecialize ("HΦ" with "Hin").
    iExists vt, vs, mt, ms.
    iSplitR. 1: by iPureIntro.
    iSplitR. 1: by iPureIntro.
    now iAssumption.
 Qed.

  Lemma fsim_source_stuck G ϕ t j i s :
    ⊢ ⌜stuck Pₛ s⌝ -∗
      fsim_lfp G ϕ t j i s.
  Proof.
    iIntros "H".
    rewrite fsim_lfp_unfold.
    iIntros "Hin".
    do 1 iRight. now iLeft.
  Qed.

  Lemma fsim_source_steps G ϕ t j i s :
    ⊢ (sim_inv t s ==∗
       ∃ s' i', ⌜Pₛ ⊨ s ->> s'⌝ ∗ sim_inv t s' ∗ fsim_lfp G ϕ t j i' s') -∗
    fsim_lfp G ϕ t j i s.
  Proof.
    iIntros "Hs".
    rewrite fsim_lfp_unfold.
    iIntros "Hin".
    do 2 iRight. iLeft.
    now iApply ("Hs" with "Hin").
  Qed.

  Lemma fsim_target_steps G ϕ t j i s :
    can_progress Pₜ t ->
    ⊢ (∀ t',
         ⌜Pₜ ⊨ t ->> t'⌝ -∗
         sim_inv t s ==∗
         sim_inv t' s ∗ ∃ j', fsim_lfp G ϕ t' j' i s) -∗
      fsim_lfp G ϕ t j i s.
  Proof.
    iIntros (H) "Ht".
    rewrite fsim_lfp_unfold.
    iIntros "Hin".
    do 3 iRight. iLeft.
    iSplitR.
    - by iPureIntro.
    - iModIntro. iIntros (t' Hstep).
      by iApply ("Ht" with "[//] Hin").
  Qed.

  Lemma fsim_progress G ϕ t j i s:
    ∀ j' i',
    j' ⊏ j ->
    i' ⊏ i ->
    ⊢ (sim_inv t s ==∗ G ϕ t j' i' s) -∗
      fsim_lfp G ϕ t j i s.
  Proof.
    iIntros (j' i' Hj Hi) "Hf".
    rewrite fsim_lfp_unfold.
    iIntros "Hin".
    iMod ("Hf" with "Hin") as "Hf".
    do 4 iRight.
    iExists j', i'. iFrame. by iPureIntro.
  Qed.

  Lemma fsim_lfp_ind (P R: sim_rel):
    ⊢ (□ ∀ ϕ t j i s,
         fsim_body R (fun ϕ t j i s => P ϕ t j i s ∧ fsim_lfp R ϕ t j i s) ϕ t j i s -∗
         P ϕ t j i s) -∗
    ∀ ϕ t j i s, fsim_lfp R ϕ t j i s -∗ P ϕ t j i s.
  Proof.
    iIntros "#IH" (ϕ t j i s) "H".
    rewrite fsim_lfp_eq.
    unfold fsim_lfp. unfold curry5.
    set (Pcur := uncurry5 P). change (P ϕ t j i s) with (Pcur (ϕ, t, j, i, s)).
    iApply (least_fixpoint_ind _ Pcur with "[] H").
    clear.
    iIntros "!>" ([[[[ϕ t] j] i] s]) "H"; simpl.
    iApply ("IH" with "H").
  Qed.

  Lemma fsim_lfp_mono gfp gfp' ϕ t j i s :
    ⊢ □ (∀ ϕ t j i s, gfp ϕ t j i s -∗ gfp' ϕ t j i s) -∗
      fsim_lfp gfp ϕ t j i s -∗
      fsim_lfp gfp' ϕ t j i s.
  Proof.
    iIntros "#Hgfp Hsim".
    iApply (fsim_lfp_ind with "[] Hsim"); clear.
    iIntros "!>" (ϕ t j i s) "IH".
    rewrite fsim_lfp_unfold.
    iApply (fsim_body_mono with "Hgfp [] IH").
    clear ϕ t j i s. iIntros "!>" (? ? ? ? ?) "H".
    by iApply bi.and_elim_l.
  Qed.

  Local Definition fsim_lfp_mono_inv R ϕ t j i s : PROP :=
    ∀ ϕ' j' i',
    □ (∀ vt vs, ϕ vt vs -∗ ϕ' vt vs) -∗
    ⌜j ⊑ j'⌝ -∗
    ⌜i ⊑ i'⌝ -∗
    fsim_lfp R ϕ' t j' i' s.

  Lemma fsim_lfp_mono_strong gfp gfp' ϕ ϕ' t j j' i i' s :
    ⊢ □ (∀ ϕ ϕ' t j j' i i' s,
           □ (∀ vt vs, ϕ vt vs -∗ ϕ' vt vs) -∗
           ⌜j ⊑ j'⌝ -∗
           ⌜i ⊑ i'⌝ -∗
           gfp ϕ t j i s -∗
           gfp' ϕ' t j' i' s) -∗
      □ (∀ vt vs, ϕ vt vs -∗ ϕ' vt vs) -∗
      ⌜j ⊑ j'⌝ -∗
      ⌜i ⊑ i'⌝ -∗
      fsim_lfp gfp ϕ t j i s -∗
      fsim_lfp gfp' ϕ' t j' i' s.
  Proof.
    iIntros "#Hgfp Hpost Hj Hi Hsim".
    iAssert (fsim_lfp_mono_inv gfp' ϕ t j i s) with "[Hsim]" as "H".
    {
      iApply (fsim_lfp_ind (fsim_lfp_mono_inv gfp') with "[] Hsim").
      clear.
      iIntros "!>" (ϕ t j i s) "IH".
      iIntros (ϕ' j' i') "Hpost Hj Hi".
      rewrite fsim_lfp_unfold.
      iApply (fsim_body_mono_strong with "Hgfp [] Hpost Hj Hi IH").
      clear.
      iIntros "!>" (ϕ ϕ' t j j' i i' s) "Hpost Hj Hi H".
      iDestruct "H" as "[IH _]".
      by iApply ("IH" with "Hpost Hj Hi").
    }
    by iApply ("H" with "Hpost Hj Hi").
  Qed.

  Local Instance fsim_gfp_def_mono :
    BiMonoPred (fun gfp => uncurry5 (fsim_lfp (curry5 gfp))).
  Proof.
    constructor.
    intros gfp1 gfp2. iIntros "#Hgfp" (x).
    destruct x as ((((ϕ & t) & j) & i) & s); simpl.
    iApply (fsim_lfp_mono).
    clear. iIntros "!>" (ϕ t j i s) "H".
    by iApply ("Hgfp" with "H").
  Qed.

  (** * Free Simulation Greatest-Fixpoint closed *)

  Local Definition fsim_gfp_def : sim_rel  :=
    curry5 (bi_greatest_fixpoint (fun gfp => uncurry5 (fsim_lfp (curry5 gfp)))).

  Local Lemma fsim_gfp_def_unfold ϕ t j i s :
    fsim_gfp_def ϕ t j i s ≡ fsim_lfp fsim_gfp_def ϕ t j i s.
  Proof.
    unfold fsim_gfp_def at 1.
    unfold curry5 at 1.
    rewrite greatest_fixpoint_unfold.
    unfold uncurry5 at 1.
    reflexivity.
  Qed.

  Local Lemma fsim_gfp_def_fixpoint ϕ t j i s:
    fsim_gfp_def ϕ t j i s ≡ fsim_body fsim_gfp_def fsim_gfp_def ϕ t j i s.
  Proof.
    rewrite fsim_gfp_def_unfold fsim_lfp_unfold.
    iSplit.
    - iIntros "H". iApply (fsim_body_mono with "[] [] H"); auto.
      iIntros "!>" (? ? ? ? ?) "H".
      now iApply (fsim_gfp_def_unfold).
    - iIntros "H". iApply (fsim_body_mono with "[] [] H"); auto.
      iIntros "!>" (? ? ? ? ?) "H".
      now iApply (fsim_gfp_def_unfold).
  Qed.

  (** * Free Simulation *)

  Local Definition fsim_aux : seal fsim_gfp_def.
  Proof. by eexists. Qed.
  Definition fsim := unseal fsim_aux.
  Local Lemma fsim_eq : fsim = fsim_gfp_def.
  Proof. unfold fsim. by rewrite (seal_eq fsim_aux). Qed.

  Lemma fsim_fixpoint ϕ t j i s:
    fsim ϕ t j i s ≡ fsim_lfp fsim ϕ t j i s.
  Proof. rewrite fsim_eq. by apply fsim_gfp_def_unfold. Qed.

  Lemma fsim_coind_strong (P: sim_rel) :
    ⊢ (□ ∀ ϕ t j i s,
         P ϕ t j i s -∗
         fsim_lfp
           (λ ϕ t j i s, P ϕ t j i s ∨ fsim ϕ t j i s) ϕ t j i s
      ) -∗
    ∀ ϕ t j i s, P ϕ t j i s -∗ fsim ϕ t j i s.
  Proof.
    iIntros "#CIH" (ϕ t j i s) "HP".
    rewrite fsim_eq. unfold  fsim_gfp_def, curry5.
    set (Pcur := uncurry5 P).
    change (P ϕ t j i s) with (Pcur (ϕ, t, j, i, s)).
    iApply (greatest_fixpoint_coind _ Pcur with "[] HP").
    clear.
    iIntros "!>" ([[[[ϕ t] j] i] s]) "HP"; simpl.
    by iApply ("CIH" with "HP").
  Qed.

  Lemma fsim_coind (P: sim_rel) :
    ⊢ (□ ∀ R ϕ t j i s,
         (□ ∀ ϕ t j j' i i' s,
            P ϕ t j i s -∗
            ⌜j ⊏ j'⌝ -∗
            ⌜i ⊏ i'⌝ -∗
            fsim_lfp R ϕ t j' i' s) -∗
         P ϕ t j i s -∗
         fsim_lfp R ϕ t j i s) -∗
    ∀ ϕ t j i s, P ϕ t j i s -∗ fsim ϕ t j i s.
  Proof.
    iIntros "#CIH" (ϕ t j i s) "HP".
    iApply (fsim_coind_strong with "[] HP").
    clear. iIntros "!>" (ϕ t j i s) "HP".
    iApply ("CIH" with "[] HP").
    clear. iIntros "!>" (ϕ t j j' i i' s) "HP %Hj %Hi".
    iApply ((fsim_progress _ _ _ _ _ _ _ _ Hj Hi)).
    iIntros "Hin".
    by iLeft.
  Qed.

  Local Definition fsim_mono_coind_inv ϕ' t j' i' s : PROP :=
    ∃ ϕ j i,
      □ (∀ vt vs, ϕ vt vs -∗ ϕ' vt vs) ∗
      ⌜j ⊑ j'⌝ ∗
      ⌜i ⊑ i'⌝ ∗
      fsim_gfp_def ϕ t j i s.

  Lemma fsim_mono ϕ ϕ' t j j' i i' s:
    ⊢ □ (∀ vt vs, ϕ vt vs -∗ ϕ' vt vs) -∗
      ⌜j ⊑ j'⌝ -∗
      ⌜i ⊑ i'⌝ -∗
      fsim ϕ t j i s -∗
      fsim ϕ' t j' i' s.
  Proof.
    iIntros "Hmon Hj Hi Hsim".
    iApply (fsim_coind_strong fsim_mono_coind_inv).
    {
      clear.
      iIntros "!>" (ϕ' t j' i' s) "H".
      iDestruct "H" as (ϕ j i) "(Hmon & Hj & Hi & Hsim)".
      rewrite fsim_gfp_def_unfold.
      iApply (fsim_lfp_mono_strong with "[] Hmon Hj Hi Hsim").
      clear.
      iIntros "!>" (ϕ ϕ' t j j' i i' s) "Hmon Hj Hi Hsim".
      iLeft. iExists ϕ, j, i. now iFrame.
    }
    rewrite fsim_eq. iExists ϕ, j, i. now iFrame.
  Qed.

End FSimDef.
