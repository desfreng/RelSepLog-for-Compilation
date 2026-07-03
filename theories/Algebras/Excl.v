From RSL Require Import Prelude.
From RSL Require Export Algebras.RA.
From RSL Require Export Algebras.BaseRA.

Inductive excl (A : Type) :=
| Excl : A -> excl A
| ExclInvalid : excl A.

Global Arguments Excl {_} _.
Global Arguments ExclInvalid {_}.

Abbreviation excl' A := (option (excl A)).
Abbreviation Excl' x := (Some (Excl x)).
Abbreviation ExclInvalid' := (Some ExclInvalid).

Instance eq_dec_agree `{EqDecision A} : EqDecision (excl A).
Proof. solve_decision. Qed.

Global Instance maybe_Excl {A} : Maybe (@Excl A) :=
  fun x => match x with Excl a => Some a | _ => None end.

Section excl.
  Context (A : Type) `{EqDecision A}.

  Implicit Types a b : A.
  Implicit Types x y : excl A.

  Global Instance Excl_inj : Inj (=) (=) (@Excl A).
  Proof using Type. by inversion_clear 1. Qed.

  Local Instance excl_valid_instance : Valid (excl A) :=
    fun x => match x with Excl _ => True | ExclInvalid => False end.

  Local Instance excl_pcore_instance : PCore (excl A) :=
    fun _ => None.
  Local Instance excl_op_instance : Op (excl A) := λ x y, ExclInvalid.

  Lemma excl_ra_mixin : RaMixin (excl A).
  Proof using Type.
    constructor.
    - by intros [] [] [].
    - by intros [] [].
    - discriminate.
    - discriminate.
    - discriminate.
    - by intros [] [].
  Qed.

  Canonical Structure exclRA := Ra (excl A) excl_ra_mixin.

  Lemma excl_included x y : x ≼ y ↔ y = ExclInvalid.
  Proof using Type.
    split.
    - destruct x, y; intros [[] Hxy]; by inv Hxy.
    - intros ->. by exists ExclInvalid.
  Qed.

  Lemma Excl_included a b : Excl' a ≼ Excl' b ↔ a = b.
  Proof using Type.
    split; [|by intros ->]. by intros [[c|] Hb%(inj Some)]; inversion_clear Hb.
  Qed.

  Lemma ExclInvalid_included ea : ea ≼ ExclInvalid.
  Proof using Type. by exists ExclInvalid. Qed.

  Lemma excl_op_inv x y : ✓ (x ⋅ y) -> False.
  Proof using Type. easy. Qed.

  Lemma excl_op_eq a x y : Excl a = x ⋅ y <-> False.
  Proof using Type. easy. Qed.

  Lemma excl_op_eq' a x y : x ⋅ y = Excl a <-> False.
  Proof using Type. easy. Qed.

  Global Instance excl_exclusive x : Exclusive x.
  Proof using Type. by destruct x; intros n []. Qed.
End excl.
