From RSL Require Import Prelude.

From RSL.Commons Require Export Values.

From stdpp Require Import gmap.
From stdpp Require Export fin_maps.

(* [memory] is a mapping from location to a value *)
Definition memory := (gmap loc val).

Instance memory_inhabited : Inhabited memory := populate ∅.

Definition get_at (addr: val) (m: memory) : option val :=
  match addr with
  | VPtr l => m !! l
  | _ => None
  end.

Definition set_at (addr: val) (v: val) (m: memory) : option memory :=
  match addr with
  | VPtr l =>
      match m !! l with
      | None => None
      | Some _ => Some (<[l := v]> m)
      end
  | _ => None
  end.

Lemma get_at_union_left l (m1 m2: memory) :
  m2 !! l = None ->
  get_at (VPtr l) (m1 ∪ m2) = get_at (VPtr l) m1.
Proof.
  intros Hmem; simpl. by apply lookup_union_l.
Qed.

Lemma get_at_union_right l (m1 m2: memory) :
  m1 !! l = None ->
  get_at (VPtr l) (m1 ∪ m2) = get_at (VPtr l) m2.
Proof.
  intros Hmem; simpl. by apply lookup_union_r.
Qed.

Lemma get_at_singl l v :
  get_at (VPtr l) {[ l := v ]} = Some v.
Proof.
  now apply lookup_singleton_eq.
Qed.

Lemma set_at_some l v old m:
  get_at (VPtr l) m = Some old ->
  set_at (VPtr l) v m = Some (<[l := v]> m).
Proof.
  unfold set_at, get_at.
  intros Hget.
  destruct (m !! l) as [[]|]; congruence.
Qed.

Lemma set_at_none addr v m:
  get_at addr m = None ->
  set_at addr v m = None.
Proof.
  unfold set_at, get_at.
  intros Hget.
  destruct addr; auto.
  by rewrite Hget.
Qed.
