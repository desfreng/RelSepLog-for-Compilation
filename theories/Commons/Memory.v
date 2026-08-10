From RSL Require Import Prelude.

From RSL.Commons Require Export Values.

From stdpp Require Import gmap.
From stdpp Require Export fin_maps.

Variant mem_cell : Type :=
  | Freed
  | Allocated (v: val).

(* [memory] is a mapping from location to a value *)
Definition memory := (gmap loc mem_cell).

Instance memory_inhabited : Inhabited memory := populate ∅.

Definition get_at (addr: val) (m: memory) : option val :=
  match addr with
  | VPtr l =>
      match m !! l with
      | None => None
      | Some Freed => None
      | Some (Allocated v) => Some v
      end
  | _ => None
  end.

Definition update_at (addr: val) (v: mem_cell) (m: memory) : option memory :=
  match addr with
  | VPtr l =>
      match m !! l with
      | None => None
      | Some Freed => None
      | Some (Allocated _) => Some (<[l := v]> m)
      end
  | _ => None
  end.

Definition set_at (addr: val) (v: val) (m: memory) : option memory :=
  update_at addr (Allocated v) m.

Definition alloc_at (l: loc) (v: val) (m: memory) : option memory :=
  match m !! l with
  | None => Some (<[l := Allocated v]> m)
  | Some _ => None
  end.

Definition free_at (addr: val) (m: memory) : option memory :=
  update_at addr Freed m.

Lemma get_at_union_left l (m1 m2: memory) :
  m2 !! l = None ->
  get_at (VPtr l) (m1 ∪ m2) = get_at (VPtr l) m1.
Proof.
  intros Hmem. simpl. unfold memory.
  by rewrite lookup_union_l.
Qed.

Lemma get_at_union_right l (m1 m2: memory) :
  m1 !! l = None ->
  get_at (VPtr l) (m1 ∪ m2) = get_at (VPtr l) m2.
Proof.
  intros Hmem. simpl. unfold memory.
  by rewrite lookup_union_r.
Qed.

Lemma get_at_singl l v :
  get_at (VPtr l) {[ l := Allocated v ]} = Some v.
Proof.
  simpl. unfold memory.
  by rewrite lookup_singleton_eq.
Qed.

Lemma update_at_some l v old m:
  get_at (VPtr l) m = Some old ->
  update_at (VPtr l) v m = Some (<[l := v]> m).
Proof.
  unfold update_at, get_at.
  intros Hget.
  destruct (m !! l) as [[]|]; congruence.
Qed.

Lemma update_at_none addr v m:
  get_at addr m = None ->
  update_at addr v m = None.
Proof.
  unfold update_at, get_at.
  intros Hget.
  repeat case_match; auto.
  congruence.
Qed.

Lemma alloc_at_is_some l v m m':
  alloc_at l v m = Some m' <->
  m' = m ∪ {[ l := Allocated v ]} ∧ m !! l = None.
Proof.
  unfold alloc_at, get_at, memory.
  split.
  - intros Hget.
    case_match eqn:Hin; first congruence.
    inv Hget. split; last done.
    replace m with (m ∪ ∅) at 1.
    + by rewrite (insert_union_r m ∅).
    + by apply map_union_empty.
  - intros [Hm HnIn].
    rewrite HnIn.
    f_equal.
    replace m with (m ∪ ∅).
    + by rewrite (insert_union_r m ∅).
    + by apply map_union_empty.
Qed.
