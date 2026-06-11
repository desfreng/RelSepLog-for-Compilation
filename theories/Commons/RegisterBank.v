From RSL Require Import Prelude.

From stdpp Require Import gmap.

Definition reg := nat.

(* [regmap] is a mapping from registers to a value *)
Definition regbank : Type := gmap reg val.

Definition get_reg (ρ: regbank) (r: reg) : val :=
  match ρ !! r with
  | Some v => v
  | None => 0%Z (* Default val *)
  end.

Definition set_reg (ρ: regbank) (r: reg) (v: val) : regbank :=
  <[r := v]>ρ.

(** ** Logical Connectives  *)

Class LogicRegisterAssert (R V : Type) :=
  regbank_assert : regbank -> R -> V -> Prop.

Instance regbank_assert_single : LogicRegisterAssert reg val :=
  fun ρ key val => get_reg ρ key = val.

Instance regbank_assert_list : LogicRegisterAssert (list reg) (list val) :=
  fun ρ keys vals => map (get_reg ρ) keys = vals.

Notation "ρ @ r '⇒' v" :=
  (regbank_assert ρ r%nat v%Z)
    (at level 60, no associativity).

Definition regbank_same (ρ1: regbank) (r1: reg) (ρ2: regbank) (r2: reg) : Prop :=
  ∃ v, ρ1 @ r1 ⇒ v ∧ ρ2 @ r2 ⇒ v.

Notation "ρ1 @ r1 '<=>' ρ2 @ r2" :=
  (regbank_same ρ1 r1%nat ρ2 r2%nat)
    (at level 60, ρ2 at next level, no associativity).

Notation "'⟦' r '⇐' v '⟧' ρ" :=
  (set_reg ρ r%nat v%Z)
    (at level 20, ρ at level 20, right associativity).

Lemma regbank_assert_unfold ρ :
  ∀ r v tl tv,
  ρ @ r ⇒ v ->
  ρ @ tl ⇒ tv ->
  ρ @ (r :: tl) ⇒ (v :: tv).
Proof.
  intros r v tl tv.
  unfold regbank_assert, regbank_assert_single, regbank_assert_list.
  intros Hv Htl. simpl.
  f_equal.
  - assumption.
  - eassumption.
Qed.

Lemma regbank_assert_nil ρ :
  ρ @ [] ⇒ [].
Proof. now unfold regbank_assert, regbank_assert_list. Qed.

Lemma regbank_set_discard ρ :
  ∀ r1 r2 v1 v2,
  r2 ≠ r1 ->
  ρ @ r1 ⇒ v1 ->
  ⟦r2 ⇐ v2⟧ρ @ r1 ⇒ v1.
Proof.
  intros r1 r2 v1 v2 Hneq.
  unfold regbank_assert, regbank_assert_single, set_reg, get_reg.
  intros Hr.
  unfold regbank in *.
  now rewrite lookup_insert_ne.
Qed.

Lemma regbank_set_use ρ :
  ∀ r v,
  ⟦r ⇐ v⟧ρ @ r ⇒ v.
Proof.
  intros r v.
  unfold regbank_assert, regbank_assert_single, set_reg, get_reg.
  unfold regbank in *.
  now rewrite lookup_insert_eq.
Qed.

Lemma regbank_never_empty ρ:
  ∀ r : reg,
  ∃ v, ρ @ r ⇒ v.
Proof.
  intros r.
  unfold regbank_assert, regbank_assert_single, get_reg.
  destruct (ρ !! r); now eexists.
Qed.
