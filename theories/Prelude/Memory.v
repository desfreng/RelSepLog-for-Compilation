From Stdlib Require Import ZArith.

From stdpp Require Import gmap.

Definition val : Type := Z.
Definition loc : Type := positive.

(* [memory] is a mapping from location to a value *)
Definition memory := (gmap loc val).

Definition loc_to_val (l: loc) : val := Zpos l.

Definition val_to_loc (v: val) : option loc :=
  if (v >=? 1)%Z
  then Some (Z.to_pos v)
  else None.

Definition get_at (addr: val) (m: memory) : option val :=
  match val_to_loc addr with
  | Some l => m !! l
  | None => None
  end.

Definition set_at (addr: val) (v: val) (m: memory) : option memory :=
  match val_to_loc addr with
  | Some l =>
      match m !! l with
      | None => None
      | Some _ => Some (alter (fun _ => v) l m)
      end
  | None => None
  end.
