From Stdlib Require Import ZArith.

From stdpp Require Import gmap.

Definition val : Type := Z.
Definition loc : Type := positive.

(* [memory] is a mapping from location to a value *)
Definition memory : Type := gmap loc val.

Definition loc_to_val (l: loc) : val := Zpos l.

Definition val_to_loc (v: val) : option loc :=
  if (v >=? 1)%Z
  then Some (Z.to_pos v)
  else None.

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

Lemma get_at_unfold : ∀ addr m v,
  get_at addr m = Some v ->
  ∃ l, val_to_loc addr = Some l ∧ m !! l = Some v.
Proof using Type.
  intros addr m v H.
  unfold get_at in H.
  case_match; try congruence.
  eexists. split; eassumption || reflexivity.
Qed.

Lemma update_at_unfold : ∀ addr f m m',
  update_at addr f m = Some m' ->
  ∃ l old,
    val_to_loc addr = Some l ∧
    m !! l = Some old ∧
    <[l := f old]>m = m'.
Proof using Type.
  intros addr f m m' H.
  unfold update_at in H.
  case_match eqn:Hloc; try congruence.
  case_match eqn:Hmem; try congruence.
  do 2 eexists. repeat split.
  - eassumption.
  - now inv H.
Qed.
