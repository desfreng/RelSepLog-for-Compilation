From RSL Require Import Prelude.

From RSL.Commons Require Export Memory.

From RSL.Logic Require Export BI.
From RSL.Logic Require Import rPropDef Tactic.

Program Definition tgt_points_to  loc v : rProp :=
  {| rProp_holds mt ms := mt = {[ loc := v ]} ∧ ms = ∅ |}.

Program Definition src_points_to loc v : rProp :=
  {| rProp_holds mt ms := mt = ∅ ∧ ms = {[ loc := v ]} |}.

Notation "l '→ₜ' v" :=
  (tgt_points_to l%positive v%Z)
    (at level 70, no associativity, format "l →ₜ v") : bi_scope.

Notation "l '→ₛ' v" :=
  (src_points_to l%positive v%Z)
    (at level 70, no associativity, format "l →ₛ v") : bi_scope.

From Ltac2 Require Import Ltac2 Printf.

Lemma tgt_points_to_unique lt1 lt2 v1 v2:
  lt1 →ₜ v1 -∗
  lt2 →ₜ v2 -∗
  ⌜lt1 ≠ lt2⌝.
Proof.
  unfold tgt_points_to, src_points_to.
  unseal. simpl.
  unseal.
  intros ? ? [-> ->] ? ? _ _ [H1 ->] ? ? Hd _ [H2 _] ->.
  apply map_disjoint_union_r in Hd as [_ Hd].
  apply map_disjoint_dom in Hd. subst.
  eapply Hd; eapply elem_of_dom, lookup_singleton_is_Some; reflexivity.
Qed.

Lemma src_points_to_unique ls1 ls2 v1 v2:
  ls1 →ₛ v1 -∗
  ls2 →ₛ v2 -∗
  ⌜ls1 ≠ ls2⌝.
Proof.
  unfold tgt_points_to, src_points_to.
  unseal. simpl. unseal.
  intros ? ? [-> ->] ? ? _ _ [-> H1] ? ? _ Hd [_ H2] ->.
  apply map_disjoint_union_r in Hd as [_ Hd].
  apply map_disjoint_dom in Hd. subst.
  eapply Hd; eapply elem_of_dom, lookup_singleton_is_Some; reflexivity.
Qed.
