From RSL Require Import Prelude.

From stdpp Require Export fin_maps fin_map_dom.

(** ** Logic Definition  *)

Definition rlogic : Type :=
  memory -> memory -> Prop.

(* Notations scope *)
Declare Scope rlogic_scope.
Delimit Scope rlogic_scope with rlogic.
Bind Scope rlogic_scope with rlogic.

(** ** Logical Connectives *)

Section LogicOp.

  Definition rlogic_and (P Q: rlogic) : rlogic :=
    fun mt ms => P mt ms ∧ Q mt ms.

  Definition rlogic_sep (P Q: rlogic) : rlogic :=
    fun mt ms =>
      ∃ mtP msP mtQ msQ,
        mtP ##ₘ mtQ ∧
        msP ##ₘ msQ ∧
        mtP ∪ mtQ = mt ∧
        msP ∪ msQ = ms ∧
        P mtP msP ∧
        Q mtQ msQ.

  Definition rlogic_or (P Q: rlogic) : rlogic :=
    fun mt ms => P mt ms ∨ Q mt ms.

  Definition rlogic_impl (P Q: rlogic) : rlogic :=
    fun mt ms => P mt ms -> Q mt ms.

  Definition rlogic_wand (P Q: rlogic) : rlogic :=
    fun mt ms =>
      ∀ mtP msP,
      mtP ##ₘ mt ->
      msP ##ₘ ms ->
      P mtP msP ->
      Q (mtP ∪ mt) (msP ∪ ms).

  Definition rlogic_not (P: rlogic) : rlogic :=
    fun mt ms => ~ P mt ms.

  Definition rlogic_exist {X: Type} (f: X -> rlogic) : rlogic :=
    fun mt ms => ∃ x, f x mt ms.

  Definition rlogic_forall {X: Type} (f: X -> rlogic) : rlogic :=
    fun mt ms => ∀ x, f x mt ms.

  Definition rlogic_empty : rlogic :=
    fun mt ms => mt = ∅ ∧ ms = ∅.

  Definition rlogic_pure (P: Prop) : rlogic :=
    fun mt ms => rlogic_empty mt ms ∧ P.

  Definition rlogic_entails (P Q: rlogic) : Prop :=
    ∀ mt ms, P mt ms -> Q mt ms.

  Definition rlogic_all_memory : rlogic :=
    fun _ _ => True.

End LogicOp.

Notation "x ∧ y" :=
  (rlogic_and x y)
    (at level 80, y constr at level 80, right associativity) : rlogic_scope.

Notation "x ∗ y" :=
  (rlogic_sep x y)
    (at level 80, y constr at level 80, right associativity) : rlogic_scope.

Notation "x ∨ y" :=
  (rlogic_or x y)
    (at level 85, y constr at level 85, right associativity) : rlogic_scope.

Notation "x -> y" := (rlogic_impl x y)
  (at level 99, y at level 200, right associativity) : rlogic_scope.

Notation "x -∗ y" := (rlogic_wand x y)
  (at level 99, y at level 200, right associativity) : rlogic_scope.

Notation "~ x" :=
  (rlogic_not x)
    (at level 75, x constr at level 75, right associativity) : rlogic_scope.

Notation "¬ x" :=
  (rlogic_not x)
    (at level 75, x constr at level 75, right associativity) : rlogic_scope.

Notation "∀ x .. y , P" :=
  (rlogic_forall (fun x => .. (rlogic_forall (fun y => P)) ..))
    (at level 10, x binder, y binder, P at level 200,
     format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : rlogic_scope.

Notation "∃ x .. y , P" :=
  (rlogic_exist (fun x => .. (rlogic_exist (fun y => P)) ..))
    (at level 10, x binder, y binder, P at level 200,
     format "'[ ' '[ ' ∃ x .. y ']' , '/' P ']'") : rlogic_scope.

Notation "⌜ P ⌝" :=
  (rlogic_pure P) (at level 0, format "⌜ P ⌝") : rlogic_scope.

Notation "⦇ P ⦈" :=
  (P)%rlogic (at level 0, P at level 200, format "⦇ P ⦈").

Notation "P ⊩ Q" :=
  (rlogic_entails P%rlogic Q%rlogic) (at level 99, right associativity).

Notation "⌜⌝" := (rlogic_empty) (at level 0) : rlogic_scope.

Abbreviation emp := (rlogic_empty).

Abbreviation GC := (rlogic_all_memory).

Lemma add_true_l P :
  P ⊩ P ∗ ⌜⌝.
Proof.
  intros mt ms HP.
  exists mt, ms, ∅, ∅. repeat split.
  - apply map_disjoint_empty_r.
  - apply map_disjoint_empty_r.
  - apply map_union_empty.
  - apply map_union_empty.
  - assumption.
Qed.

Lemma add_true_r P :
  P ⊩ ⌜⌝ ∗ P.
Proof.
  intros mt ms HP.
  exists ∅, ∅, mt, ms. repeat split.
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
  - apply map_empty_union.
  - apply map_empty_union.
  - assumption.
Qed.

Lemma remove_true_l P :
  P ∗ ⌜⌝ ⊩ P.
Proof.
  intros mt ms HP.
  destruct HP as (mtP & msP & ? & ? & ? & ? & <- & <- & HP & Hemp).
  destruct Hemp as [-> ->].
  rewrite !(map_union_empty _).
  assumption.
Qed.

Lemma entails_refl P :
  P ⊩ P.
Proof.
  now intros mt ms HP.
Qed.

Global Instance entails_refl_inst : Reflexive rlogic_entails := entails_refl.

Lemma sep_comm P Q :
  P ∗ Q ⊩ Q ∗ P.
Proof.
  intros mt ms (mtP & msP & mtQ & msQ & Ht & Hs & Hcupt & Hcups & HP & HQ).
  subst.
  exists mtQ, msQ, mtP, msP.
  repeat split.
  - solve_map_disjoint.
  - solve_map_disjoint.
  - apply map_union_comm. solve_map_disjoint.
  - apply map_union_comm. solve_map_disjoint.
  - assumption.
  - assumption.
Qed.

Lemma sep_pure_left P Q :
  P -> Q ⊩ ⌜P⌝ ∗ Q.
Proof.
  intros HP mt ms HQ.
  exists ∅, ∅, mt, ms. repeat split.
  - solve_map_disjoint.
  - solve_map_disjoint.
  - apply map_empty_union.
  - apply map_empty_union.
  - assumption.
  - assumption.
Qed.
