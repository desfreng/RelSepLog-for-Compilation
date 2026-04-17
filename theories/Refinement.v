From stdpp Require Import prelude.

From Coinduction Require Import all.

From RSL.Commons Require Import Language.

(* Set Mangle Names. *)

Section Refinement.
  Context {Λ: language}.

  Definition observation : Type := value Λ -> value Λ -> Prop.

  Context {Obs: observation} `{!PreOrder Obs}.

  Program Definition diverges_: mon (state Λ -> Prop) :=
    {| body R s := ∃ s', step s s' ∧ R s' |}.
  Next Obligation. firstorder. Qed.

  Definition diverges : state Λ -> Prop := gfp diverges_.

  Lemma diveges_sound : ∀ f,
    (∀ n, step (f n) (f (S n))) -> diverges (f 0).
  Proof.
    intros f Hf. cut (∀ n, diverges (f n)); auto.
    unfold diverges. coinduction R cih.
    intros n. exists (f (S n)); auto.
  Qed.

  Variant behavior :=
  | Terminating (v: value Λ)
  | Diverging
  | Unknown.

  Inductive behavior_order : behavior -> behavior -> Prop :=
  | TerminatingOrder : ∀ vₜ vₛ,
    Obs vₜ vₛ -> behavior_order (Terminating vₜ) (Terminating vₛ)
  | DivergingOrder : behavior_order Diverging Diverging
  | UnkownOrder : ∀ s, behavior_order s Unknown.

  Instance beh_pre_order : PreOrder behavior_order.
  Proof.
    split.
    - intros []; now constructor.
    - intros x y z Hxy Hyz. inv Hxy; inv Hyz; constructor.
      etransitivity; eassumption.
  Qed.

  Instance behavior_order_notation : SqSubsetEq behavior := behavior_order.

  (* [beh s] is the set of all the behaviors of [s] *)
  Inductive beh : state Λ -> behavior -> Prop :=
  | IsTerminating : ∀ s v,
      is_final s = Some v ->
      beh s (Terminating v)
  | IsDiverging : ∀ s,
      diverges s ->
      beh s Diverging
  | IsStuck : ∀ s,
      stuck s ->
      beh s Unknown
  | IsSteping : ∀ s t b,
      beh t b ->
      step s t ->
      beh s b.

  Instance beh_elem_state : ElemOf behavior (state Λ) := λ b s, beh s b.

  (* [s] is terminating iff there is a execution from [s] to a final state. *)
  Lemma has_terminating_behavior : ∀ s v,
    Terminating v ∈ s <-> ∃ t, rtc step s t ∧ is_final t = Some v.
  Proof.
    intros s v. split; intros Hbeh.
    - remember (Terminating v) as b eqn:Hb.
      induction Hbeh as [ s | | | s t b ? IH Hstep ]; inv Hb; auto.
      + exists s. now constructor.
      + destruct (IH eq_refl) as (t' & Hrtc & Hfin). clear IH.
        exists t'. split; eauto. now apply rtc_l with t.
    - destruct Hbeh as (t & Hrtc & Hfin).
      induction Hrtc as [ | s t u Hstep Hrtc IH ].
      + now constructor.
      + eapply IsSteping; eauto. now apply IH.
  Qed.

  (* [s] is diverging iff [s] has a diverging execution *)
  Lemma has_diverging_behavior : ∀ s,
    Diverging ∈ s <-> diverges s.
  Proof.
    intros s. split; intros Hbeh.
    - revert s Hbeh. unfold diverges. coinduction R cih.
      intros s Hbeh. inv Hbeh.
      + apply (gfp_pfp diverges_) in H.
        destruct H as (s' & Hstep & Hdiv).
        exists s'. split; auto. apply cih. apply IsDiverging. assumption.
      + exists t. split; auto.
    - now apply IsDiverging.
  Qed.

  (* [s] has a unknown behavior if [s] reduces to a stuck state. *)
  Lemma has_stuck_behavior : ∀ s,
    Unknown ∈ s <-> ∃ t, rtc step s t ∧ stuck t.
  Proof.
    intros s. split; intros Hbeh.
    - remember Unknown as b eqn:Hb.
      induction Hbeh as [ | | s | s t b ? IH Hstep ]; inv Hb; auto.
      + exists s. now split.
      + destruct (IH eq_refl) as (u & Hrtc & Hstuck).
        exists u. split.
        * now apply rtc_l with t.
        * assumption.
    - destruct Hbeh as (u & Hrtc & Hstuck).
      induction Hrtc  as [ | s t u Hstep Hrtc IH].
      + now constructor.
      + eapply IsSteping.
        * now apply IH.
        * easy.
  Qed.
End Refinement.

(* A definition of state refinement:
   - if the target terminates on (v, m),
   the source must either terminate on (v, m) or be stuck.
   - if the target diverges,
   the source must either diverges or be stuck.
   - if the target is stuck, the source should also be stuck.
 *)
(* Definition refines (t: state Λ) (s: state Λ) := *)
(*   ∀ b, b ∈ t -> ∃ b', b' ∈ s ∧ b ⊑ b'. *)

(* Instance refines_preorder : PreOrder refines. *)
(* Proof. *)
(*   split. *)
(*   - intros s b Hb. exists b. now split. *)
(*   - intros s t u Hst Htu b Hb. *)
(*     destruct (Hst _ Hb) as (b' & Hb' & ?). *)
(*     destruct (Htu _ Hb') as (b'' & Hb'' & ?). *)
(*     exists b''. split. *)
(*       + assumption. *)
(*       + etransitivity; eassumption. *)
(* Qed. *)
