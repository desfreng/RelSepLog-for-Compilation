From Stdlib Require Import ZArith.

From stdpp Require Import gmap.

Definition val : Type := Z.
Definition loc : Type := positive.

(* [memory] is a mapping from location to a value *)
Abbreviation memory := (gmap loc val).

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
     | Some loc => Some (alter f loc m)
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
  ∃ loc,
    val_to_loc addr = Some loc ∧
    alter f loc m = m'.
Proof using Type.
  intros addr f m m' H.
  unfold update_at in H.
  case_match eqn:Hloc; try congruence.
  eexists. split.
  - reflexivity.
  - now inv H.
Qed.

Lemma alter_union_left f loc (m1 m2: memory) :
  m1 ##ₘ m2 ->
  m2 !! loc = None ->
  alter f loc (m1 ∪ m2) = alter f loc m1 ∪ m2.
Proof using Type.
  intros Hdij Hnin.
  unfold union, map_union.
  rewrite (alter_union_with_l _ _ m1).
  - reflexivity.
  - intros x y H1 H2. exfalso.
    rewrite map_disjoint_alt in Hdij.
    destruct (Hdij loc) as [? | ?]; congruence.
  - intros x H1 H2. congruence.
Qed.

Lemma alter_union_right f loc (m1 m2: memory) :
  m1 ##ₘ m2 ->
  m1 !! loc = None ->
  alter f loc (m1 ∪ m2) = m1 ∪ alter f loc m2.
Proof using Type.
  intros Hdij Hnin.
  unfold union, map_union.
  rewrite (alter_union_with_r _ _ m1).
  - reflexivity.
  - intros x y H1 H2. exfalso.
    rewrite map_disjoint_alt in Hdij.
    destruct (Hdij loc) as [? | ?]; congruence.
  - intros x H1 H2. congruence.
Qed.
