From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Notations.

From RSL Require Import Simulations.FreeSim.
From RSL Require Import Simulations.FreeSimRules.

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
      fun '(vt, mt) '(vs, ms) => (Q vt vs) mt ms
    in
    fun mt ms => fsim_lfp C Φ ([], st, mt) j i ([], ss, ms).

  Definition hoare C P st j i ss Q : rlogic :=
    (□ ∀ Φ, P -∗
             (∀ vt vs, Q vt vs -∗ Φ vt vs) -∗
             sim C st j i ss Φ)%I.

  Notation
    "'[' C ']' st '<{' j ',' i '}=' ss '{{' Q '}}'" :=
    (sim C st j i ss Q%I)
      (at level 0, no associativity).

  Notation
    "'[' C ']' '{{' P '}}' st  '<{' j ',' i '}=' ss '{{' Q '}}'" :=
    (hoare C P%I st j i ss Q%I)
      (at level 0, no associativity).

  Lemma both_ret C ρₜ ρₛ fₜ pcₜ j i fₛ pcₛ Q :
    ∀ rₜ vₜ rₛ vₛ,
    fₜ@pcₜ is <<{ ret rₜ }>> ->
    fₛ@pcₛ is <<{ ret rₛ }>> ->
    ρₜ @ rₜ ⇒ vₜ ->
    ρₛ @ rₛ ⇒ vₛ ->
    Q vₜ vₛ ⊢ [C] State fₜ pcₜ ρₜ <{j, i}= State fₛ pcₛ ρₛ {{ Q }}.
  Proof using Type.
    intros rt vt rs vs Hpct Hpcs Ht Hs.
    repeat unseal.
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

  Local Definition coind_inv
    (Inv: (val → val → rlogic) -> pcstate -> pcstate -> rlogic)
    (ϕ: value Λₜ → value Λₛ → Prop)
    (t: state Λₜ) (j i: nat) (s: state Λₛ) : Prop :=
    ∃ mt st ms ss,
      t = ([], st, mt) ∧
      s = ([], ss, ms) ∧
      Inv (fun vt vs mt ms => ϕ (vt, mt) (vs, ms)) st ss mt ms.

  Lemma coind Inv st j i ss Q :
    ⊢ □ (∀ R st i j ss,
           □ (∀ st j' i' ss,
                ⌜i < i'⌟ -∗
                ⌜j < j'⌟ -∗
                Inv Q st ss -∗
                [R] st <{j', i'}= ss {{ Q }}) -∗
        Inv Q st ss -∗
        [R] st <{j, i}= ss {{ Q }}
      ) -∗
      Inv Q st ss -∗
      [fsim] st <{j, i}= ss {{ Q }}.
  Proof using Type.
    unfold sim; unseal.
    intros ? ? [-> ->] ? ? _ _ [[-> ->] RIH].
    intros mtInv msInv _ _ Hinv.
    eapply (coind_strong_open nat nat Pₜ Pₛ _ (coind_inv Inv)).
    {
      clear Hinv st ss i j mtInv msInv.
      intros R ? j i ? CIH (mt & st & ms & ss & -> & -> & Hinv).
      rewrite <- (map_empty_union mt).
      rewrite <- (map_empty_union ms).
      rewrite <- (map_empty_union ∅).
      eapply RIH; auto; try solve_map_disjoint.
      split. { easy. }
      intros ? ? [-> ->] st' j' i' ss'.
      intros ? ? _ _ [[-> ->] Hi].
      intros ? ? _ _ [[-> ->] Hj].
      intros mtInv msInv _ _ Hinv'.
      apply CIH; auto.
      exists mtInv, st', msInv, ss'.
      repeat split.
      - now rewrite !(map_empty_union _).
      - now rewrite !(map_empty_union _).
      - assumption.
    }
    exists mtInv, st, msInv, ss.
    repeat split.
    - now rewrite !(map_empty_union _).
    - now rewrite !(map_empty_union _).
    - assumption.
  Qed.
End RulesDef.
