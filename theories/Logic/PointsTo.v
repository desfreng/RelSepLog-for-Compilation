From RSL Require Import Prelude.

From RSL.Commons Require Export Memory.

From RSL.Logic Require Export BI.
From RSL.Logic Require Import rPropDef Tactic.

Program Definition tgt_points_to loc v : rProp :=
  {| rProp_holds mt ms := mt = {[ loc := Allocated v ]} ∧ ms = ∅ |}.

Program Definition src_points_to loc v : rProp :=
  {| rProp_holds mt ms := mt = ∅ ∧ ms = {[ loc := Allocated v ]} |}.

Notation "l '→ₜ' v" :=
  (tgt_points_to l%positive v%Z)
    (at level 70, no associativity, format "l →ₜ v") : bi_scope.

Notation "l '→ₛ' v" :=
  (src_points_to l%positive v%Z)
    (at level 70, no associativity, format "l →ₛ v") : bi_scope.

Program Definition tgt_freed loc : rProp :=
  {| rProp_holds mt ms := mt = {[ loc := Freed ]} ∧ ms = ∅ |}.

Program Definition src_freed loc : rProp :=
  {| rProp_holds mt ms := mt = ∅ ∧ ms = {[ loc := Freed ]} |}.

Notation "'freeₜ' l" :=
  (tgt_freed l%positive)
    (at level 70) : bi_scope.

Notation "'freeₛ' l" :=
  (src_freed l%positive)
    (at level 70) : bi_scope.

Lemma tgt_points_to_unique l1 l2 v1 v2:
  l1 →ₜ v1 -∗
  l2 →ₜ v2 -∗
  ⌜l1 ≠ l2⌝.
Proof.
  unfold tgt_points_to, src_points_to, tgt_freed, src_freed.
  unseal.
  intros ? ? [-> ->] ? ? _ _ [H1 ->] ? ? Hd _ [H2 _] ->.
  apply map_disjoint_union_r in Hd as [_ Hd].
  apply map_disjoint_dom in Hd. subst.
  eapply Hd; eapply elem_of_dom, lookup_singleton_is_Some; reflexivity.
Qed.

Lemma tgt_freed_unique l1 l2:
  freeₜ l1 -∗
  freeₜ l2 -∗
  ⌜l1 ≠ l2⌝.
Proof.
  unfold tgt_points_to, src_points_to, tgt_freed, src_freed.
  unseal.
  intros ? ? [-> ->] ? ? _ _ [H1 ->] ? ? Hd _ [H2 _] ->.
  apply map_disjoint_union_r in Hd as [_ Hd].
  apply map_disjoint_dom in Hd. subst.
  eapply Hd; eapply elem_of_dom, lookup_singleton_is_Some; reflexivity.
Qed.

Lemma tgt_points_to_freed_unique l1 l2 v:
  l1 →ₜ v -∗
  freeₜ l2 -∗
  ⌜l1 ≠ l2⌝.
Proof.
  unfold tgt_points_to, src_points_to, tgt_freed, src_freed.
  unseal.
  intros ? ? [-> ->] ? ? _ _ [H1 ->] ? ? Hd _ [H2 _] ->.
  apply map_disjoint_union_r in Hd as [_ Hd].
  apply map_disjoint_dom in Hd. subst.
  eapply Hd; eapply elem_of_dom, lookup_singleton_is_Some; reflexivity.
Qed.

Lemma src_points_to_unique l1 l2 v1 v2:
  l1 →ₛ v1 -∗
  l2 →ₛ v2 -∗
  ⌜l1 ≠ l2⌝.
Proof.
  unfold tgt_points_to, src_points_to.
  unseal. simpl. unseal.
  intros ? ? [-> ->] ? ? _ _ [-> H1] ? ? _ Hd [_ H2] ->.
  apply map_disjoint_union_r in Hd as [_ Hd].
  apply map_disjoint_dom in Hd. subst.
  eapply Hd; eapply elem_of_dom, lookup_singleton_is_Some; reflexivity.
Qed.

Lemma src_freed_unique l1 l2:
  freeₛ l1 -∗
  freeₛ l2 -∗
  ⌜l1 ≠ l2⌝.
Proof.
  unfold tgt_points_to, src_points_to, tgt_freed, src_freed.
  unseal.
  intros ? ? [-> ->] ? ? _ _ [-> H1] ? ? _ Hd [_ H2] ->.
  apply map_disjoint_union_r in Hd as [_ Hd].
  apply map_disjoint_dom in Hd. subst.
  eapply Hd; eapply elem_of_dom, lookup_singleton_is_Some; reflexivity.
Qed.

Lemma src_points_to_freed_unique l1 l2 v:
  l1 →ₛ v -∗
  freeₛ l2 -∗
 ⌜l1 ≠ l2⌝.
Proof.
  unfold tgt_points_to, src_points_to, tgt_freed, src_freed.
  unseal.
  intros ? ? [-> ->] ? ? _ _ [-> H1] ? ? _ Hd [_ H2] ->.
  apply map_disjoint_union_r in Hd as [_ Hd].
  apply map_disjoint_dom in Hd. subst.
  eapply Hd; eapply elem_of_dom, lookup_singleton_is_Some; reflexivity.
Qed.
