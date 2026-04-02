From Stdlib Require Import Utf8.

From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.Relations.

From RSL Require Import NatMap.
From RSL Require Import RTL.
From RSL Require Import Notations.
From RSL Require Import Semantics.
From RSL Require Import Tactics.

Import RTLNotations.
Import ListNotations.

(* Set Mangle Names. *)

Section WP.
  Variable P : program.

  Definition postcondition : Type := val -> memory -> Prop.

  Inductive final (Q: postcondition) : state -> Prop :=
  | Final : ∀ v m, Q v m -> final Q ([], ReturnState v, m).

  Definition safe (Q: postcondition) (s: state) : Prop :=
    ∀ t, P ⊢ s ->>* t -> final Q t ∨ ∃ u, P ⊢ t ->> u.

  Definition wp (f: function) (pc: node) (Q: postcondition)
    : regmap * memory -> Prop :=
    fun '(ρ, m) => safe Q ([], State f pc ρ, m).

  Lemma wp_ret f pc Q : forall v,
    f@pc is <{ ret v }> ->
    ∀ ρ m, Q (get_reg ρ v) m -> wp f pc Q (ρ, m).
  Proof.
    intros v H ρ m.
    unfold wp, safe.
    intros Hwp t Hred.
    destruct (inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc )].
    - right. eexists. econstructor; now eauto.
    - inv Hreds; try congruence.
      destruct (inv_step _ _ _ Hrtc) as [ <- | (? & Hwhat & ? )].
      + pc_inj. left. constructor. assumption.
      + inversion Hwhat.
  Qed.

  Lemma wp_nop f pc Q : forall pc',
    f@pc is <{ nop -> pc' }> ->
    ∀ ρ m, wp f pc' Q (ρ, m) -> wp f pc Q (ρ, m).
  Proof.
    intros pc' H ρ m.
    unfold wp, safe.
    intros Hwp t Hred.
    destruct (inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc )].
    - right. eexists. econstructor; now eauto.
    - apply Hwp; inv Hreds; pc_inj; congruence.
  Qed.

  Lemma wp_op f pc Q : forall dst op args pc',
    f@pc is <{ dst := @op args -> pc' }> ->
    ∀ ρ m,
    (∃ v,
        eval_op op (get_regs ρ args) = Some v
        ∧ wp f pc' Q (set_reg ρ dst v, m)
    ) -> wp f pc Q (ρ, m).
  Proof.
    intros dst op args pc' H ρ m.
    unfold wp, safe.
    intros (v & Hv & Hwp) t Hred.
    destruct (inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc )].
    - right. eexists. econstructor; now eauto.
    - apply Hwp; inv Hreds; pc_inj; congruence.
  Qed.

  Lemma wp_load f pc Q : forall dst src pc',
    f@pc is <{ dst := !src -> pc' }> ->
    ∀ ρ m,
    (
      let addr := get_reg ρ src in
      ∃ v, get_at m addr = Some v ∧  wp f pc' Q (set_reg ρ dst v, m)
    ) -> wp f pc Q (ρ, m).
  Proof.
    intros dst src pc' H ρ m.
    unfold wp, safe.
    intros (v & Hv & Hwp) t Hred.
    destruct (inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc )].
    - right. eexists. econstructor; now eauto.
    - apply Hwp; inv Hreds; pc_inj; try congruence.
  Qed.

  Lemma wp_store f pc Q : forall dst src pc',
    f@pc is <{ !dst := src -> pc' }> ->
    ∀ ρ m,
    (
      let addr := get_reg ρ dst in
      let v := get_reg ρ src in
      ∃ m', set_at m addr v = Some m' ∧ wp f pc' Q (ρ, m')
    ) -> wp f pc Q (ρ, m).
  Proof.
    intros dst src pc' H ρ m.
    unfold wp, safe.
    intros (v & Hv & Hwp) t Hred.
    destruct (inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc )].
    - right. eexists. econstructor; now eauto.
    - apply Hwp; inv Hreds; pc_inj; congruence.
  Qed.

  Lemma wp_cond f pc Q : forall cond ifso ifnot,
    f@pc is <{ if cond then goto ifso else goto ifnot }> ->
    ∀ ρ m,
    (
      if (get_reg ρ cond =? 0)%Z
      then wp f ifso Q (ρ, m)
      else wp f ifnot Q (ρ, m)
    ) -> wp f pc Q (ρ, m).
  Proof.
    intros cond ifso ifnot H ρ m.
    unfold wp, safe.
    intros Hwp t Hred.
    destruct (inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc)].
    - right. eexists. econstructor; now eauto.
    - inv Hreds; pc_inj; try congruence.
      destruct (get_reg ρ cond =? 0)%Z eqn:Hcond; auto.
  Qed.

  Definition precondition : Type := list val -> memory -> Prop.

  Definition hoare (P: precondition) (f: function) (Q: postcondition) : Prop
    := ∀ args m, P args m -> safe Q ([], CallState f args, m).

  Notation "'{{' P '}}' f '{{' Q '}}'" :=
    (hoare P f Q) (at level 90, f at next level).

  Lemma wp_call f pc Q : ∀ dst sig args pc',
    f@pc is <{ dst := @call sig args -> pc' }> ->
    ∀ ρ m,
    (∃ fn Pre Post,
        let vals := get_regs ρ args in
        find_fun P sig = Some fn ∧
        {{ Pre }} fn {{ Post }} ∧
        Pre vals m ∧
        ∀ v m', let ρ' := set_reg ρ dst v in
                Post v m' -> wp f pc' Q (ρ', m')
    ) -> wp f pc Q (ρ, m).
  Proof.
    intros dst sig args pc' H ρ m.
    unfold wp, safe.
    intros (fn & Pre & Post & Hfun & Hspec & Hpre & Hwp) t Hred.
    destruct (inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc)].
    - right. eexists. econstructor; now eauto.
    - inv Hreds; pc_inj; try congruence. pc_inj.
      destruct t as [[σ' s] m''] eqn:Ht.
      destruct (unfold_call _ _ _ _ _ _ _ _ _ _  _ Hrtc)
        as [(σ'' & Hσ & Hrtc') | (v & m' & Hrtc' & Hrest)].
      + destruct (Hspec _ _ Hpre _ Hrtc') as [Hfin | (u & Hu)].
        * inv Hfin; simpl. right. eexists. econstructor; now eauto.
        * right. destruct u as [[]?]. subst.
          eexists. apply lift_step. apply Hu.
      + destruct (Hspec _ _ Hpre _ Hrtc') as [Hfin | (u & Hu)].
        * inv Hfin; simpl. eapply Hwp; eassumption.
        * inversion Hu.
  Qed.
End WP.

Section WP2.
  Variable P : program.
  (* Definition stuck s := ~ (∃ t, P ⊢ s ->> t) ∧ ~ (final s). *)

  (* Definition not_stuck s := final s ∨ ∃ t, P ⊢ s ->> t. *)

  Fixpoint wp2_ (n: nat) (s: state) (Q: postcondition) :=
    match n with
    | O => True
    | S n =>
        (final Q s) ∨ ((∃ t, P ⊢ s ->> t) ∧ ∀ t, P ⊢ s ->> t -> wp2_ n t Q)
    end.

  Definition wp2 (s: state) (Q: postcondition) := ∀ n, wp2_ n s Q.

  Lemma safe_to_wp2 : ∀ s Q,
    safe P Q s -> wp2 s Q.
  Proof.
    intros s Q H n. induction n as [ | n IH] in H, s |- *.
    - easy.
    - simpl. destruct (H s (rt_refl _ _ _)) as [Hfin | [t Ht]].
      + auto.
      + right. split.
        * exists t. assumption.
        * intros u Hu. apply IH. intros v Hv. apply H.
          eapply rt_trans.
          -- constructor. eassumption.
          -- assumption.
  Qed.

  Lemma wp2_acc : ∀ s t Q,
    P ⊢ s ->>* t ->
    wp2 s Q ->
    wp2 t Q.
  Proof.
    intros s t Q Hst.
    induction Hst as [ s t H | s | s t u Hs IHs Ht IHt]; intros Hw.
    - intros n. specialize (Hw (S n)). simpl in Hw.
      destruct Hw as [Hfin | [_ Hall]].
      + inversion Hfin; subst. inversion H.
      + apply Hall. exact H.
    - exact Hw.
    - apply IHt. apply IHs. exact Hw.
  Qed.

  Lemma wp2_to_safe : ∀ s Q,
    wp2 s Q -> safe P Q s.
  Proof.
    intros s Q Hwp. unfold wp2, safe.
    intros t Hred.
    apply (wp2_acc _ _ Q) in Hred; try assumption.
    specialize (Hred 1). simpl in Hred.
    destruct Hred as [?| [ ]]; auto.
  Qed.

  Theorem wp2_is_safe :
    ∀ s Q, wp2 s Q <-> safe P Q s.
  Proof.
    intros s Q. split.
    - apply wp2_to_safe.
    - apply safe_to_wp2.
  Qed.
End WP2.

