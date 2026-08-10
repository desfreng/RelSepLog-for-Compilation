From RSL Require Import Prelude.

From stdpp Require Import gmap.

Definition loc : Type := positive.
Definition loc_pair : Type := gset (loc * loc).

Variant val : Type :=
| VInt (v: Z)
| VBool (b : bool)
| VPtr (l : loc)
| VUndef.

Definition related (I: loc_pair) l1 l2 :=
  (l2, l1) ∈ I.

Variant same_val I : val -> val -> Prop :=
  | IntEq i1 i2 :
    i1 = i2 ->
    same_val I (VInt i1) (VInt i2)

  | BoolEq b1 b2 :
    b1 = b2 ->
    same_val I (VBool b1) (VBool b2)

  | PtrEq p1 p2 :
    related I p1 p2 ->
    same_val I (VPtr p1) (VPtr p2)

  | UndefEq v :
    same_val I v VUndef.

Lemma same_val_mono I I' vt vs :
  I ⊆ I' ->
  same_val I vt vs ->
  same_val I' vt vs.
Proof using Type.
  intros Hincl Hsame.
  inv Hsame; econstructor; auto.
  by apply Hincl.
Qed.
