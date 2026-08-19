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

Lemma get_at_mono addr m v:
  get_at addr m = Some v ->
  ∀ mm, get_at addr (m ∪ mm) = Some v.
Proof.
  unfold get_at, memory.
  intros Hget mm.
  case_match eqn:Haddr; try congruence.
  case_match eqn:Hlookup; try congruence.
  case_match eqn:Hcell; try congruence.
  inv Hget.
  by apply (lookup_union_Some_l m mm) in Hlookup as ->.
Qed.

Lemma update_at_mono addr m v m':
  update_at addr v m = Some m' ->
  ∀ mm, update_at addr v (m ∪ mm) = Some (m' ∪ mm).
Proof.
  unfold update_at, memory.
  intros Hget mm.
  case_match eqn:Haddr; try congruence.
  case_match eqn:Hlookup; try congruence.
  case_match eqn:Hcell; try congruence.
  inv Hget.
  apply (lookup_union_Some_l m mm) in Hlookup as ->.
  f_equal. by apply insert_union_l.
Qed.

Lemma alloc_at_mono l m v m':
  alloc_at l v m = Some m' ->
  ∀ mm,
  m' ##ₘ mm ->
  alloc_at l v (m ∪ mm) = Some (m' ∪ mm).
Proof.
  unfold alloc_at, memory.
  intros Hget mm Hdij.
  case_match eqn:Hlookup; try congruence.
  inv Hget.
  apply map_disjoint_insert_l in Hdij as [HnIn Hdij].
  case_match eqn:Hin.
  - apply lookup_union_Some in Hin as []; try congruence. done.
  - f_equal. by apply insert_union_l.
Qed.

Lemma update_at_dom addr v m m':
  update_at addr v m = Some m' ->
  dom m = dom m'.
Proof.
  unfold update_at, memory in *.
  intros H.
  case_match eqn:Haddr; try congruence.
  case_match eqn:Hlookup; try congruence.
  case_match eqn:Hcell; try congruence.
  inv H.
  symmetry.
  by eapply dom_insert_lookup_L.
Qed.

Lemma alloc_at_dom l v m m':
  alloc_at l v m = Some m' ->
  {[ l ]} ∪ dom m = dom m'.
Proof.
  unfold alloc_at, memory in *.
  intros H.
  case_match eqn:Hlookup; try congruence.
  inv H. by rewrite dom_insert_L.
Qed.

Lemma alloc_at_not_in l v m m':
  alloc_at l v m = Some m' -> m !! l = None.
Proof.
  unfold alloc_at, memory in *.
  intros H.
  by case_match eqn:Hlookup.
Qed.

Lemma can_alloc m v: ∃ l, is_Some (alloc_at l v m).
Proof.
  pose (l := fresh (dom m)).
  exists l.
  unfold alloc_at.
  assert (m !! l = None) as -> by (apply not_elem_of_dom, is_fresh).
  done.
Qed.
