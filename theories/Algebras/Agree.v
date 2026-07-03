From RSL Require Import Prelude.
From RSL Require Export Algebras.RA.

Inductive agree (A: Type) :=
| Ag (a : A)
| AgBot.

Arguments Ag {_} _.
Arguments AgBot {_}.

Instance eq_dec_agree `{EqDecision A} : EqDecision (agree A).
Proof. solve_decision. Qed.

Section agree.
  Context (A : Type) {eq_dec : EqDecision A}.

  Implicit Types a b : A.
  Implicit Types x y : agree A.

  Local Instance agree_op_instance : Op (agree A) := fun x y =>
    match x, y with
    | Ag a, Ag b => if eq_dec a b then Ag a else AgBot
    | _, _ => AgBot
    end.

  Local Instance agree_pcore_instance : PCore (agree A) := fun x => Some x.

  Local Instance agree_valid_instance : Valid (agree A) := fun x =>
    match x with
    | Ag _ => True
    | AgBot => False
    end.

  Lemma agree_comm x y : x ⋅ y = y ⋅ x.
  Proof using Type.
    destruct x as [a|], y as [b|]; unfold op; simpl; auto.
    destruct (eq_dec a b), (eq_dec b a); congruence.
  Qed.

  Lemma agree_assoc x y z : x ⋅ (y ⋅ z) = (x ⋅ y) ⋅ z.
  Proof using Type.
    destruct x as [a|], y as [b|], z as [c|]; unfold op; simpl; auto.
    - destruct (eq_dec b c), (eq_dec a b); simpl; destruct (eq_dec a c); congruence.
    - destruct (eq_dec a b); simpl; congruence.
  Qed.

  Lemma agree_idemp x : x ⋅ x = x.
  Proof using Type.
    destruct x as [a|]; unfold op; simpl; auto.
    destruct (eq_dec a a); congruence.
  Qed.

  Lemma agree_included x y : x ≼ y <-> y = x ⋅ y.
  Proof using Type.
    split.
    - by intros [z Hz]; rewrite Hz, agree_assoc, agree_idemp.
    - by intros ?; exists y.
  Qed.

  Lemma agree_op_inv x y : ✓ (x ⋅ y) → x = y.
  Proof using Type.
    destruct x as [a|], y as [b|]; unfold valid, op; simpl; try contradiction.
    destruct (eq_dec a b); contradiction || congruence.
  Qed.

  Definition agree_ra_mixin : RaMixin (agree A).
  Proof using Type.
    constructor; try apply _ || by auto.
    - by apply agree_assoc.
    - by apply agree_comm.
    - by intros x cx H; inv H; apply agree_idemp.
    - by intros x y cx Hlt H; inv H; exists y.
    - unfold op, valid; intros [] y H; rewrite <- (agree_op_inv _ _ H) in H;
      simpl in *; auto.
  Qed.

  Canonical Structure agreeRA : ra := Ra (agree A) agree_ra_mixin.

  Global Instance agree_ra_total : RaTotal agreeRA.
  Proof using Type. unfold RaTotal; eauto. Qed.

  Global Instance agree_core_id x : CoreId x.
  Proof using Type. by constructor. Qed.

  Lemma agree_pcore x : pcore x = Some x.
  Proof using Type. done. Qed.

  Global Instance Ag_inj : Inj (=) (=) (@Ag A).
  Proof using Type.
    by intros a b H; injection H.
  Qed.

  Lemma Ag_uninj x : ✓ x → ∃ a, Ag a = x.
  Proof using Type.
    destruct x; unfold valid; simpl; eauto. contradiction.
  Qed.

  Lemma agree_valid_included x y : ✓ y → x ≼ y → x = y.
  Proof using Type.
    intros Hval [z Hy]; revert Hval; rewrite Hy.
    intro H. now rewrite (agree_op_inv _ _ H), agree_idemp.
  Qed.

  Lemma Ag_included a b : Ag a ≼ Ag b ↔ a = b.
  Proof using Type.
    split; last by intros ->.
    intros. by apply (inj Ag), agree_valid_included.
  Qed.

  Lemma Ag_op_inv a b : ✓ (Ag a ⋅ Ag b) → a = b.
  Proof using Type. by intros ?%agree_op_inv%(inj Ag). Qed.

  Lemma Ag_op_valid a b : ✓ (Ag a ⋅ Ag b) ↔ a = b.
  Proof using Type.
    split; first by apply Ag_op_inv.
    intros ->. by rewrite agree_idemp.
  Qed.

  Lemma Ag_valid a : ✓ (Ag a).
  Proof using Type. easy. Qed.

  Lemma Ag_op_eq a b c : Ag a = Ag b ⋅ Ag c <-> a = b ∧ b = c.
  Proof using Type.
    split.
    - intros H.
      assert (Hac: c = a) by (by apply Ag_included; eexists; rewrite ra_comm).
      assert (Hab: b = a) by (by apply Ag_included; eexists).
      split; congruence.
    - intros [-> ->]. symmetry. apply agree_idemp.
  Qed.

  Lemma Ag_op_eq_inv x y a : Ag a = x ⋅ y <-> x = Ag a ∧ y = Ag a.
  Proof using Type.
    split.
    - intros H. destruct x, y; inv H as [Hag].
      apply Ag_op_eq in Hag. destruct Hag.
      split; congruence.
    - intros [-> ->]. symmetry. apply agree_idemp.
  Qed.

  Lemma Ag_op_eq' a b c : Ag b ⋅ Ag c = Ag a <-> a = b ∧ b = c.
  Proof using Type.
    split.
    - intros H. now apply Ag_op_eq.
    - intros [-> ->]. apply agree_idemp.
  Qed.

  Lemma Ag_op_eq_inv' x y a : x ⋅ y = Ag a <-> x = Ag a ∧ y = Ag a.
  Proof using Type.
    split.
    - intros H. now apply Ag_op_eq_inv.
    - intros [-> ->]. apply agree_idemp.
  Qed.

  Global Instance agree_cancelable x : Cancelable x.
  Proof using Type.
    intros y z Hv Heq.
    destruct (Ag_uninj x) as [x' EQx]; first by eapply ra_valid_op_l.
    destruct (Ag_uninj y) as [y' EQy]; first by eapply ra_valid_op_r.
    destruct (Ag_uninj z) as [z' EQz].
    { eapply (ra_valid_op_r x z). by rewrite <-Heq. }
    assert (Hx'y' : x' = y').
    { apply (inj Ag), agree_op_inv. by rewrite EQx, EQy. }
    assert (Hx'z' : x' = z').
    { apply (inj Ag), agree_op_inv. rewrite EQx, EQz.
      unfold op in *. simpl in *. by rewrite <-Heq.
    }
    congruence.
  Qed.

End agree.
