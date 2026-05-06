From stdpp Require Import prelude.

From Stdlib Require Import Classical.

From Coinduction Require Import all.

From RSL Require Import Commons.Utils.
From RSL Require Import Commons.Language.

(* Set Mangle Names. *)

Section Behavior.
  Context {Λ: lang} (P: prog Λ).
  Implicit Type s : state Λ.

  Program Definition diverges_: mon (state Λ -> Prop) :=
    {| body R s := ∃ s', P ⊨ s ->> s' ∧ R s' |}.
  Next Obligation. firstorder. Qed.

  Definition diverges : state Λ -> Prop := gfp diverges_.

  Lemma diveges_sound : ∀ f,
    (∀ n, P ⊨ f n ->> f (S n)) -> diverges (f 0).
  Proof.
    intros f Hf. cut (∀ n, diverges (f n)); auto.
    unfold diverges. coinduction R cih.
    intros n. exists (f (S n)); auto.
  Qed.

  Lemma diverges_unroll : ∀ t,
    diverges t -> ∃ t', P ⊨ t ->> t' ∧ diverges t'.
  Proof.
    intros t H. unfold diverges in H. apply (gfp_fp diverges_) in H.
    inv H. eexists; now eauto.
  Qed.

  Lemma diverge_iff : ∀ s,
    (∀ t, P ⊨ s ->>* t -> ∃ u, P ⊨ t ->> u) <->
    ∀ t, P ⊨ s ->>* t -> diverges t.
  Proof.
    intros s. split.
    - intros Hs. unfold diverges. coinduction R cih.
      intros t Hrtc. destruct (Hs _ Hrtc) as [u Hstep].
      exists u. split; auto.
      apply cih. eapply rtc_r; eassumption.
    - intros Hdiv t Hrtc. apply Hdiv in Hrtc.
      destruct (diverges_unroll _ Hrtc) as [u []].
      now exists u.
  Qed.

  Variant behavior :=
  | Terminating (v: value Λ)
  | Diverging
  | Unknown.

  (* [beh s] is the set of all the behaviors of [s] *)
  Inductive beh : behavior -> state Λ -> Prop :=
  | IsTerminating : ∀ s v,
      is_final s = Some v ->
      beh (Terminating v) s
  | IsDiverging : ∀ s,
      diverges s ->
      beh Diverging s
  | IsStuck : ∀ s,
      stuck P s ->
      beh Unknown s             (* Undef? *)
  | IsSteping : ∀ s t b,
      beh b t ->
      P ⊨ s ->> t ->
      beh b s.

  #[local] Instance beh_elem_state : ElemOf behavior (state Λ) := beh.

  (* [s] is terminating iff there is a execution from [s] to a final state. *)
  Lemma has_terminating_behavior : ∀ s v,
    Terminating v ∈ s <-> ∃ t, P ⊨ s ->>* t ∧ is_final t = Some v.
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
    Unknown ∈ s <-> ∃ t, P ⊨ s ->>* t ∧ stuck P t.
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

  Definition does_end s : Prop :=
    ∃ t, P ⊨ s ->>* t ∧ ((∃ v, is_final t = Some v) ∨ stuck P t).

  Lemma not_ending_diverges:
    ∀ s, ~(does_end s) -> ∀ t, P ⊨ s ->>* t -> diverges t.
  Proof.
    intros s H. unfold diverges.
    coinduction R cih.
    assert (Hs: ∀ t, P ⊨ s ->>* t -> is_final t = None ∧ ~ stuck P t).
    {
      intros t Hstep. apply not_ex_all_not with (n := t) in H.
      split.
      - destruct (is_final t) as [v | ].
        + exfalso. apply H. split; auto. left. now eexists.
        + reflexivity.
      - intro Hs. apply H. now auto.
    }
    intros t Hrtc.
    destruct (Hs t) as [Hnfin Hnstuck]; auto.
    unfold stuck in Hnstuck.
    assert (Hprogress: can_progress P t) by tauto.
    destruct (can_progress_must_step _ _ Hprogress) as [u Hstep].
    exists u. split; auto.
    apply cih. eapply rtc_r; eassumption.
  Qed.

  Theorem every_state_has_beh : ∀ s, ∃ b, b ∈ s.
  Proof.
    intros s. destruct (classic (does_end s)) as [(t & Hrtc & [[v Hfin] | H]) | H].
    - exists (Terminating v). apply has_terminating_behavior.
      exists t; auto.
    - exists Unknown. apply has_stuck_behavior.
      exists t; auto.
    - exists Diverging. apply has_diverging_behavior.
      apply not_ending_diverges with s; auto.
  Qed.
End Behavior.
