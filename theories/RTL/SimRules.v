From RSL Require Import Logic Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.FreeSim.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Notations.

Import RTLNotations.

Section RulesDef.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation fsim := (fsim WfNat WfNat Pₜ Pₛ).
  Abbreviation fsim_lfp := (fsim_lfp WfNat WfNat Pₜ Pₛ).
  Abbreviation post := (val -> val -> rlogic).

  Definition sim C ρ fₜ pcₜ j i fₛ pcₛ (Q: post) : rlogic :=
    let Φ : value Λₜ * memory -> value Λₛ * memory -> Prop :=
      fun '(vₜ, mₜ) '(vₛ, mₛ) => Q vₜ vₛ mₜ mₛ
    in
    let '(ρₜ, ρₛ) := ρ in
    fun mₜ mₛ =>
      fsim_lfp C Φ
        ([], State fₜ pcₜ ρₜ, mₜ) j i ([], State fₛ pcₛ ρₛ, mₛ).

  Definition hoare C ρ P fₜ pcₜ j i fₛ pcₛ Q : Prop :=
    let '(ρₜ, ρₛ) := ρ in
    emp ⊩ ∀ Φ, P -∗
             (∀ vₜ vₛ, Q vₜ vₛ -∗ Φ vₜ vₛ) -∗
             sim C ρ fₜ pcₜ j i fₛ pcₛ Φ.

  Notation
    "'[' C ']' ρ '⊢' ft '@' pct  '<{' j ',' i '}=' fs '@' pcs '{{' Q '}}'" :=
    (sim C ρ ft pct j i fs pcs Q%rlogic)
      (at level 0, ft at level 0, fs at level 0, no associativity).

  Notation
    "'[' C ']' ρ '⊢' '{{' P '}}' ft '@' pct  '<{' j ',' i '}=' fs '@' pcs '{{' Q '}}'" :=
    (hoare C ρ P%rlogic ft pct j i fs pcs Q%rlogic)
      (at level 0, ft at level 0, fs at level 0, no associativity).

  Lemma both_ret C ρₜ ρₛ fₜ pcₜ j i fₛ pcₛ Q :
    ∀ rₜ vₜ rₛ vₛ,
    fₜ@pcₜ is <<{ ret rₜ }>> ->
    fₛ@pcₛ is <<{ ret rₛ }>> ->
    ρₜ @ rₜ ⇒ vₜ ->
    ρₛ @ rₛ ⇒ vₛ ->
    Q vₜ vₛ ⊩ [C] (ρₜ, ρₛ) ⊢ fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros rt vt rs vs Hpct Hpcs Ht Hs.
    intros mtQ msQ HQ.

    eapply FSourceSteps with (i' := 0).
    { eapply exec_Iret; eassumption. }

    eapply FTargetSteps.
    { eexists; eapply exec_Iret; eassumption. }

    intros t' Hstep. inv Hstep. exists 0.

    eapply FRelated.

    do 2 eexists; repeat split. simpl.
    simregs. assumption.
  Qed.

  Lemma frame C ρₜ ρₛ P1 P2 fₜ pcₜ j i fₛ pcₛ Q :
    [C] (ρₜ, ρₛ) ⊢ {{ P1 }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ fun vₜ vₛ => Q vₜ vₛ }} ->
    [C] (ρₜ, ρₛ) ⊢ {{ P1 ∗ P2 }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ fun vₜ vₛ => Q vₜ vₛ ∗ P2 }}.
  Proof using Type.
    intros H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    destruct Hpre as (mt1 & ms1 & mt2 & ms2 & ? & ? & ? & ? & HP1 & HP2).
    subst. decompose_map_disjoint.

    rewrite (map_union_comm mt1 mt2) by easy.
    rewrite (map_union_comm ms1 ms2) by easy.

    rewrite <- (map_union_assoc mt2).
    rewrite <- (map_union_assoc ms2).

    rewrite (map_union_assoc mtPost mt2).
    rewrite (map_union_assoc msPost ms2).

    apply H; try solve_map_disjoint.

    intros vₜ vₛ mt' ms' ? ? ?.
    subst. decompose_map_disjoint.

    rewrite (map_union_comm mtPost) by easy.
    rewrite (map_union_comm msPost) by easy.

    rewrite (map_union_assoc mt').
    rewrite (map_union_assoc ms').

    apply Hpost; try solve_map_disjoint.
    exists mt', ms', mt2, ms2. repeat split; solve_map_disjoint.
  Qed.

  Lemma consequence C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ P' Q',
    (P ⊩ P') ->
    (∀ vₜ vₛ, Q' vₜ vₛ ⊩ Q vₜ vₛ) ->
    [C] (ρₜ, ρₛ) ⊢ {{ P' }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q' }} ->
    [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros P' Q' HP HQ H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    subst. decompose_map_disjoint.

    apply H; try solve_map_disjoint.
    intros vₜ vₛ mt' ms' ? ? HQ'.
    apply Hpost; auto.
    now apply HQ.
  Qed.

  Local Lemma rewrite_hoare C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    (
      ∀ (Ψ: value Λₜ * memory → value Λₛ * memory → Prop) (mtP msP mtQ msQ : memory),
        ∀ Φ,
        (∀ vₜ vₛ mₜ mₛ, Φ vₜ vₛ mₜ mₛ <-> Ψ (vₜ, mₜ) (vₛ, mₛ)) ∧
        mtP ##ₘ mtQ ∧
        msP ##ₘ msQ ∧
        P mtP msP ∧
        (∀ (vₜ vₛ : val) (mt ms : memory),
           mt ##ₘ mtQ ->
           ms ##ₘ msQ ->
           Q vₜ vₛ mt ms ->
           Φ vₜ vₛ (mt ∪ mtQ) (ms ∪ msQ)
        ) ->
        fsim_lfp C (fun '(vₜ, mₜ) '(vₛ, mₛ) => Φ vₜ vₛ mₜ mₛ)
          ([], State fₜ pcₜ ρₜ, mtQ ∪ mtP) j i ([], State fₛ pcₛ ρₛ, msQ ∪ msP)
    ) <->
      [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    split; intros H.
    - intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.
      destruct Hemp as (-> & ->).
      decompose_map_disjoint.
      unfold memory in *.
      rewrite !(map_union_empty _).
      apply H with (Ψ := fun '(vₜ, mₜ) '(vₛ, mₛ) => Ψ vₜ vₛ mₜ mₛ).
      repeat split; easy.
    - intros Ψ mtP msP mtQ msQ Φ (HΦ & Ht & Hs & Hpre & Hpost).
      rewrite <- (map_union_empty mtP).
      rewrite <- (map_union_empty msP).
      apply H.
      + now split.
      + solve_map_disjoint.
      + solve_map_disjoint.
      + assumption.
      + solve_map_disjoint.
      + solve_map_disjoint.
      + intros vₜ vₛ mt ms.
        apply Hpost.
  Qed.

  Lemma coind ρₜ ρₛ Inv fₜ pcₜ j i fₛ pcₛ Q :
    (∀ R ρₜ ρₛ,
       (∀ ρₜ ρₛ j' i',
          i < i' ->
          j < j' ->
          [R] (ρₜ, ρₛ) ⊢ {{ Inv ρₜ ρₛ }} fₜ @ pcₜ <{j', i'}= fₛ @ pcₛ {{ Q }}) ->
       [R] (ρₜ, ρₛ) ⊢ {{ Inv ρₜ ρₛ }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}
    ) ->
    [fsim] (ρₜ, ρₛ) ⊢ {{ Inv ρₜ ρₛ }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros RIH.
    rewrite <- rewrite_hoare.
    intros Ψ mtP msP mtQ msQ Φ H.
    apply fsim_unroll.
    revert ρₜ ρₛ Ψ mtP msP mtQ msQ Φ H.
    coinduction C CIH.
    intros ρₜ ρₛ Ψ mtP msP mtQ msQ Φ (HΦ & Ht & Hs & Hpre & Hpost).
    rewrite <- (map_union_empty mtP).
    rewrite <- (map_union_empty msP).
    apply RIH.
    - intros ρₜ' ρₛ' j' i' Hi Hj.
      rewrite <- rewrite_hoare.
      repeat intro.
      eapply FProgress.
      { eassumption. }
      { eassumption. }
      eapply CIH. eassumption.
    - now split.
    - solve_map_disjoint.
    - solve_map_disjoint.
    - assumption.
    - solve_map_disjoint.
    - solve_map_disjoint.
    - intros vₜ vₛ mt ms. apply Hpost.
  Qed.

  Lemma iex C ρₜ ρₛ fₜ pcₜ j i fₛ pcₛ Q :
    ∀ T (P: T -> rlogic),
    (∀ x,
       [C] (ρₜ, ρₛ) ⊢ {{ P x }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}) ->
    [C] (ρₜ, ρₛ) ⊢ {{ ∃ x, P x }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros T P H.
    intros ? ? Hemp Ψ mtPre msPre ? ? (x & Hpre).
    eapply H.
    - assumption.
    - solve_map_disjoint.
    - solve_map_disjoint.
    - eassumption.
  Qed.

  Lemma ipure C ρₜ ρₛ fₜ pcₜ j i fₛ pcₛ Q :
    ∀ P1 P2,
    (P1 -> [C] (ρₜ, ρₛ) ⊢ {{ P2 }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }})
    <-> [C] (ρₜ, ρₛ) ⊢ {{ ⌜P1⌝ ∗ P2 }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros P1 P2.
    split.
    - intros H.
      intros ? ? Hemp Ψ mtPre msPre ? ? Hpre.
      destruct Hpre as
        (msP1 & mtP1 & mtP2 & msP2 & ? & ? & ? & ? & ((? & ?) & HP1) & HP2).
      subst. decompose_map_disjoint.
      eapply H.
      + assumption.
      + assumption.
      + solve_map_disjoint.
      + solve_map_disjoint.
      + unfold memory in *. now rewrite !(map_empty_union _).
    - intros H HP1.
      intros ? ? Hemp Ψ mtPre msPre ? ? Hpre.
      eapply H.
      + assumption.
      + solve_map_disjoint.
      + solve_map_disjoint.
      + do 4 eexists. repeat split; eauto.
        * solve_map_disjoint.
        * solve_map_disjoint.
        * apply map_empty_union.
        * apply map_empty_union.
  Qed.

  Lemma fsim_mono ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ j' i',
    (j' <= j)%nat ->
    (i' <= i)%nat ->
    [fsim] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j', i'}= fₛ @ pcₛ {{ Q }} ->
    [fsim] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros i' j' Hi Hj H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.
    apply (gfp_fp fsim_lfp).
    eapply idx_mono.
    4:{
      apply (gfp_chain (chain_gfp fsim_lfp)).
      apply (gfp_fp fsim_lfp).
      now apply H.
    }
    - by intros [] [].
    - unfold "⊑". simpl. lia.
    - unfold "⊑". simpl. lia.
  Qed.

End RulesDef.
