From Stdlib Require Import Utf8.

From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.

From stdpp Require Import relations.
From stdpp Require Import tactics.

From RSL Require Import RTL.
From RSL Require Import Notations.
From RSL Require Import Semantics.
From RSL Require Import Logic.
From RSL Require Import WP.

Import RTLNotations.
Import ListNotations.

Section Sim.
  Variable P: program.

  Definition exec : Type := nat → state.

  (** Asserts that f is a diverging execution from s. *)
  Definition diverging_execution (f: exec) (s: state) :=
    f 0 = s ∧ ∀ n, P ⊨ f n ->> f (S n).

  (** s is a diverging state if s is the begining of some diverging execution *)
  Definition diverges (s: state) := ∃ f, diverging_execution f s.

  Variant behavior :=
  | Terminating (v: val) (m: memory)
  | Diverging
  | Unknown.

  Inductive behavior_order : behavior -> behavior -> Prop :=
  | TerminatingOrder : ∀ v m, behavior_order (Terminating v m) (Terminating v m)
  | DivergingOrder : behavior_order Diverging Diverging
  | UnkownOrder : ∀ s, behavior_order s Unknown.

  Instance behavior_order_inst : PartialOrder behavior_order.
  Proof.
    split. 1: split.
    - intros []; constructor.
    - intros x y z Hxy Hyz. inv Hxy.
      + assumption.
      + assumption.
      + inv Hyz. constructor.
    - intros x y Hxy Hyx. inv Hxy; try reflexivity.
      now inv Hyx.
  Qed.
  Instance behavior_order_notation : SqSubsetEq behavior := behavior_order.

  (* [beh s] is the set of all the behaviors of [s] *)
  Inductive beh : state -> behavior -> Prop :=
  | IsTerminating : ∀ v m,
      beh ([], ReturnState v, m) (Terminating v m)
  | IsDiverging : ∀ s,
      diverges s ->
      beh s Diverging
  | IsStuck : ∀ s,
      stuck P s ->
      beh s Unknown
  | IsSteping : ∀ s t b,
      beh t b ->
      P ⊨ s ->> t ->
      beh s b.

  Instance beh_elem_state : ElemOf behavior (behavior -> Prop) := fun b P => P b.

  (* [s] is terminating iff there is a execution from [s] to a final state. *)
  Lemma has_terminating_behavior : ∀ s v m,
    Terminating v m ∈ beh s <-> P ⊨ s ->>* ([], ReturnState v, m).
  Proof.
    intros s v m. split; intros H.
    - remember (Terminating v m) as b eqn:Hb.
      induction H as [ | | | s t b ? IH Hstep ] in s, H, v, m, b, Hb |- *; inv Hb.
      + constructor.
      + apply rtc_l with t; now auto.
    - remember ([], ReturnState v, m) as t eqn:Ht.
      induction H as [ | s t u Hstep Hrtc IH ]
        in t, Ht, v, m, H |- *; subst.
      + constructor.
      + econstructor. 2: eassumption. firstorder.
  Qed.

  (* [s] is diverging iff [s] has a diverging execution *)
  Lemma has_diverging_behavior : ∀ s,
    Diverging ∈ beh s <-> diverges s.
  Proof.
    intros s. split; intros H.
    - remember Diverging as b eqn:Hb.
      induction H as [ | | | s t b ? IH Hstep ]
        in s, b, Hb, H |- *; try discriminate Hb; eauto.
      destruct (IH Hb) as (f & Hinit & Hsucc).
      exists (fun n => match n with O => s | S n => f n end). split.
      + reflexivity.
      + intros []; now subst.
    - now constructor.
  Qed.

  (* [s] has a unknown behavior if [s] reduces to a stuck state. *)
  Lemma has_stuck_behavior : ∀ s,
    Unknown ∈ beh s <-> ∃ t, P ⊨ s ->>* t ∧ stuck P t.
  Proof.
    intros s. split; intros H.
    - remember Unknown as b eqn:Hb.
      induction H as [ s | | | s t b ? IH Hstep ]
        in s, b, Hb, H |- *; try discriminate Hb; eauto.
      + exists s. now split.
      + destruct (IH Hb) as (u & Hrtc & Hstuck).
        exists u. split.
        * now apply rtc_l with t.
        * assumption.
    - destruct H as (u & Hrtc & Hstuck).
      induction Hrtc  as [ | s t u Hstep Hrtc IH] in s, u, Hrtc, Hstuck |- *.
      + now constructor.
      + eapply IsSteping.
        * now apply IH.
        * easy.
  Qed.

  (* A definition of state refinement:
     - if the target terminates on (v, m),
       the source must either terminate on (v, m) or be stuck.
     - if the target diverges,
       the source must either diverges or be stuck.
     - if the target is stuck, the source should also be stuck.
   *)
  Definition refines (t: state) (s: state) :=
    ∀ b, b ∈ beh t -> ∃ b', b' ∈ beh s ∧ b ⊑ b'.


End Sim.
