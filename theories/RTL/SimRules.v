From RSL Require Import RelLogic Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.FreeSim.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Notations.

From iris.proofmode Require Import proofmode.

Import RTLNotations.

Section RulesDef.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation fsim := (fsim WfNat WfNat Pₜ Pₛ).
  Abbreviation fsim_lfp := (fsim_lfp WfNat WfNat Pₜ Pₛ).
  Abbreviation post := (val -> val -> rlogic).

  Definition sim C st j i ss (Q: post) : rlogic :=
    let Φ : value Λₜ -> value Λₛ -> Prop :=
      fun '(vₜ, mₜ) '(vₛ, mₛ) => Q vₜ vₛ mₜ mₛ
    in
    fun mₜ mₛ =>
      fsim_lfp C Φ
        j ([], st, mₜ)
        i ([], ss, mₛ).

  Definition hoare C P st j i ss Q : rlogic :=
    (□ ∀ Φ, P -∗
             (∀ vₜ vₛ, Q vₜ vₛ -∗ Φ vₜ vₛ) -∗
             sim C st j i ss Φ)%I.

  Notation
    "'[' C ']' st '<{' j ',' i '}=' ss '{{' Q '}}'" :=
    (sim C st j i ss Q%I)
      (at level 0, no associativity).

  Notation
    "'[' C ']' '{{' P '}}' st  '<{' j ',' i '}=' ss '{{' Q '}}'" :=
    (hoare C P%I st j i ss Q%I)
      (at level 0, no associativity).

  (* Lemma both_ret C ρₜ ρₛ fₜ pcₜ j i fₛ pcₛ Q : *)
  (*   ∀ rₜ vₜ rₛ vₛ, *)
  (*   fₜ@pcₜ is <<{ ret rₜ }>> -> *)
  (*   fₛ@pcₛ is <<{ ret rₛ }>> -> *)
  (*   ρₜ @ rₜ ⇒ vₜ -> *)
  (*   ρₛ @ rₛ ⇒ vₛ -> *)
  (*   Q vₜ vₛ ⊢ [C] State fₜ pcₜ ρₜ <{j, i}= State fₛ pcₛ ρₛ {{ Q }}. *)
  (* Proof using Type. *)
  (*   intros rt vt rs vs Hpct Hpcs Ht Hs. *)
  (*   intros mtQ msQ HQ. *)

  (*   eapply FSourceSteps with (i' := 0). *)
  (*   { eapply exec_Iret; eassumption. } *)

  (*   eapply FTargetSteps. *)
  (*   { eexists; eapply exec_Iret; eassumption. } *)

  (*   intros t' Hstep. inv Hstep. exists 0. *)

  (*   eapply FRelated. *)

  (*   do 2 eexists; repeat split. simpl. *)
  (*   simregs. assumption. *)
  (* Qed. *)

  Lemma frame C P1 P2 st j i ss Q :
    [C] {{ P1 }} st <{j, i}= ss {{ fun vₜ vₛ => Q vₜ vₛ }}
    ⊢
    [C] {{ P1 ∗ P2 }} st <{j, i}= ss {{ fun vₜ vₛ => Q vₜ vₛ ∗ P2 }}.
  Proof using Type.
    iIntros "#H !> %Φ [HP1 HP2] Hpost".
    iApply ("H" with "HP1").
    iIntros "%vt %vs HQ".
    iApply "Hpost".
    iFrame.
  Qed.

  Lemma consequence C P P' st j i ss Q Q' :
    (P ⊢ P') ->
    (∀ vₜ vₛ, Q' vₜ vₛ ⊢ Q vₜ vₛ) ->
    [C] {{ P' }} st <{j, i}= ss {{ Q' }}
    ⊢ [C] {{ P }} st <{j, i}= ss {{ Q }}.
  Proof using Type.
    iIntros (HP HQ) "#H !> %Φ Hpre Hpost".
    iApply ("H" with "[Hpre]").
    - iApply (HP). iAssumption.
    - iIntros (vₜ vₛ) "HQ'".
      iApply "Hpost". iApply (HQ). iAssumption.
  Qed.

  (* Local Lemma rewrite_hoare C P st j i ss Q : *)
  (*   ( *)
  (*     ∀ (Ψ: value Λₜ → value Λₛ → Prop) (mtP msP mtQ msQ : memory), *)
  (*       ∀ Φ, *)
  (*       (∀ vₜ vₛ mₜ mₛ, Φ vₜ vₛ mₜ mₛ <-> Ψ (vₜ, mₜ) (vₛ, mₛ)) ∧ *)
  (*       mtP ##ₘ mtQ ∧ *)
  (*       msP ##ₘ msQ ∧ *)
  (*       P mtP msP ∧ *)
  (*       (∀ (vₜ vₛ : val) (mt ms : memory), *)
  (*          mt ##ₘ mtQ -> *)
  (*          ms ##ₘ msQ -> *)
  (*          Q vₜ vₛ mt ms -> *)
  (*          Φ vₜ vₛ (mt ∪ mtQ) (ms ∪ msQ) *)
  (*       ) -> *)
  (*       fsim_lfp C (fun '(vₜ, mₜ) '(vₛ, mₛ) => Φ vₜ vₛ mₜ mₛ) *)
  (*         j ([], st, mtQ ∪ mtP) *)
  (*         i ([], ss, msQ ∪ msP) *)
  (*   ) ⊣⊢ *)
  (*   [C] {{ P }} st <{j, i}= ss {{ Q }}. *)
  (* Proof using Type. *)
  (*   split; intros H. *)
  (*   - intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost. *)
  (*     destruct Hemp as (-> & ->). *)
  (*     decompose_map_disjoint. *)
  (*     unfold memory in *. *)
  (*     rewrite !(map_union_empty _). *)
  (*     apply H with (Ψ := fun '(vₜ, mₜ) '(vₛ, mₛ) => Ψ vₜ vₛ mₜ mₛ). *)
  (*     repeat split; easy. *)
  (*   - intros Ψ mtP msP mtQ msQ Φ (HΦ & Ht & Hs & Hpre & Hpost). *)
  (*     rewrite <- (map_union_empty mtP). *)
  (*     rewrite <- (map_union_empty msP). *)
  (*     apply H. *)
  (*     + now split. *)
  (*     + solve_map_disjoint. *)
  (*     + solve_map_disjoint. *)
  (*     + assumption. *)
  (*     + solve_map_disjoint. *)
  (*     + solve_map_disjoint. *)
  (*     + intros vₜ vₛ mt ms. *)
  (*       apply Hpost. *)
  (* Qed. *)

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
    - apply (gfp_chain (chain_gfp fsim_lfp)).
      apply (gfp_fp fsim_lfp).
      now apply H.
    - unfold "⊑". simpl. lia.
    - unfold "⊑". simpl. lia.
  Qed.

End RulesDef.
