From stdpp Require Import prelude.
From stdpp Require Import strings.
From stdpp Require Import gmap.

Definition ident : Type := string.
Definition val : Type := Z.

Definition node := nat.
Definition loc := positive.
Definition reg := nat.

(* [regmap] is a mapping from registers to a value *)
Definition regmap : Type := gmap reg val.

(* [memory] is a mapping from location to a value *)
Definition memory : Type := gmap loc val.

Definition loc_to_val (l: loc) : val := Zpos l.

Definition val_to_loc (v: val) : option loc :=
  if (v >=? 1)%Z
  then Some (Z.to_pos v)
  else None.

Definition get_reg (r: reg) (ρ: regmap) : val :=
  match ρ !! r with
  | Some v => v
  | None => 0%Z (* Dummy val *)
  end.

Definition get_regs (l: list reg) (ρ: regmap) : list val :=
  map (fun r => get_reg r ρ) l.

Definition set_reg (r: reg) (v: val) (ρ: regmap) : regmap := <[r := v]>ρ.

Definition get_at (addr: val) (m: memory) : option val :=
  match val_to_loc addr with
  | Some loc => m !! loc
  | None => None
  end.

Definition update_at (addr: val) (f: val -> val) (m: memory) : option memory
  := match val_to_loc addr with
     | Some loc =>
         match m !! loc with
         | Some old => Some (<[loc := f old]>m)
         | None => None
         end
     | None => None
     end.

Definition set_at (addr: val) (v: val) (m: memory) : option memory :=
  update_at addr (fun _ => v) m.
