From RSL Require Import Prelude.

Definition loc : Type := positive.

Variant val : Type :=
| VInt (v: Z)
| VBool (b : bool)
| VPtr (l : loc)
| VUndef.

Definition val_eq (loc_eq : loc -> loc -> Prop) (v1 v2 : val) :=
  match v1, v2 with
  | VInt i1, VInt i2 => i1 = i2
  | VBool b1, VBool b2 => b1 = b2
  | VPtr p1, VPtr p2 => loc_eq p1 p2
  | _, _ => False
  end.
