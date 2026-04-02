From Stdlib Require Import Utf8.
From Stdlib Require Import Structures.OrderedType.
From Stdlib Require Import FSets.FMaps.
From Stdlib Require Import Lia.

Module NatOrdered <: OrderedType.
  Definition t : Type := nat.

  Definition eq (x: t) (y: t) := x = y.
  Definition lt (x: t) (y: t) := x < y.

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt_trans : ∀ x y z : t, lt x y -> lt y z -> lt x z.
  Proof. unfold lt. lia. Qed.

  Definition lt_not_eq : ∀ x y : t, lt x y -> ~ eq x y.
  Proof. unfold eq, lt. lia. Qed.

  Definition compare : ∀ x y : t, Compare lt eq x y.
  Proof.
    intros x y. unfold eq, lt.
    destruct (PeanoNat.Nat.compare x y) eqn:H.
    - apply EQ. now apply PeanoNat.Nat.compare_eq_iff.
    - apply LT. now apply PeanoNat.Nat.compare_lt_iff.
    - apply GT. now apply PeanoNat.Nat.compare_gt_iff.
  Defined.

  Definition eq_dec : ∀ x y, { eq x y } + { ~ eq x y }.
  Proof.
    intros x y. destruct (compare x y).
    - right. now apply lt_not_eq.
    - now left.
    - right. symmetry. now apply lt_not_eq.
  Defined.
End NatOrdered.

Module NatMap <: S := FMapList.Make NatOrdered.
