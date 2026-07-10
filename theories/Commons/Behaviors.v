From RSL Require Import Prelude.

From RSL.Commons Require Import Language.

From Stdlib Require Import Classical.

From Coinduction Require Import all.

Section Behavior.
  Context {Λ: lang} (P: prog Λ).
  Implicit Types s : state Λ.

  Program Definition diverges_: mon (state Λ -> Prop) :=
    {| body R s := ∃ s', P ⊨ s ->> s' ∧ R s' |}.
  Next Obligation. firstorder. Qed.

  Definition diverges : state Λ -> Prop := gfp diverges_.

  Lemma diveges_sound : ∀ f,
    (∀ n, P ⊨ f n ->> f (S n)) -> diverges (f 0).
  Proof using Type.
    intros f Hf. cut (∀ n, diverges (f n)); auto.
    unfold diverges. coinduction R cih.
    intros n. exists (f (S n)); auto.
  Qed.

  Lemma diverges_unroll : ∀ t,
    diverges t -> ∃ t', P ⊨ t ->> t' ∧ diverges t'.
  Proof using Type.
    intros t H. unfold diverges in H. apply (gfp_fp diverges_) in H.
    inv H. eexists; now eauto.
  Qed.

  Lemma diverge_iff : ∀ s,
    (∀ t, P ⊨ s ->>* t -> ∃ u, P ⊨ t ->> u) <->
    ∀ t, P ⊨ s ->>* t -> diverges t.
  Proof using Type.
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
  | Terminating (v: value Λ) (m: memory)
  | Diverging
  | Undef.

  (* [beh s] is the set of all the behaviors of [s] *)
  Inductive beh : behavior -> state Λ -> Prop :=
  | IsTerminating : ∀ s v m,
      is_final s = Some (v, m) ->
      beh (Terminating v m) s
  | IsDiverging : ∀ s,
      diverges s ->
      beh Diverging s
  | IsStuck : ∀ s,
      stuck P s ->
      beh Undef s
  | IsSteping : ∀ s t b,
      beh b t ->
      P ⊨ s ->> t ->
      beh b s.

  Global Instance beh_elem_state : ElemOf behavior (state Λ) := beh.

  (* [s] is terminating iff there is a execution from [s] to a final state. *)
  Lemma has_terminating_behavior : ∀ s v m,
    Terminating v m ∈ s <-> ∃ s', P ⊨ s ->>* s' ∧ is_final s' = Some (v, m).
  Proof using Type.
    intros s v m. split; intros Hbeh.
    - remember (Terminating v m) as b eqn:Hb.
      induction Hbeh as [ s | | | s t b ? IH Hstep ]; inv Hb; auto.
      + exists s. now constructor.
      + destruct (IH eq_refl) as (s' & Hrtc & Hfin). clear IH.
        exists s'. split; eauto. now apply rtc_l with t.
    - destruct Hbeh as (s' & Hrtc & Hfin).
      induction Hrtc as [ | s ? u Hstep Hrtc IH ].
      + now constructor.
      + eapply IsSteping; eauto. now apply IH.
  Qed.

  (* [s] is diverging iff [s] has a diverging execution *)
  Lemma has_diverging_behavior : ∀ s,
    Diverging ∈ s <-> diverges s.
  Proof using Type.
    intros s. split; intros Hbeh.
    - revert s Hbeh. unfold diverges. coinduction R cih.
      intros s Hbeh. inv Hbeh as [ | ? Hdiv | | ? t ? H Hstep ].
      + apply (gfp_pfp diverges_) in Hdiv.
        destruct Hdiv as (s' & Hstep & Hdiv).
        exists s'. split; auto. apply cih. apply IsDiverging. assumption.
      + exists t. split; auto.
    - now apply IsDiverging.
  Qed.

  (* [s] has a undef behavior if [s] reduces to a stuck state. *)
  Lemma has_undef_behavior : ∀ s,
    Undef ∈ s <-> ∃ t, P ⊨ s ->>* t ∧ stuck P t.
  Proof using Type.
    intros s. split; intros Hbeh.
    - remember Undef as b eqn:Hb.
      induction Hbeh as [ | | s | s t b ? IH Hstep ]; inv Hb; auto.
      + exists s. now split.
      + destruct (IH eq_refl) as (u & Hrtc & Hstuck).
        exists u. split.
        * now apply rtc_l with t.
        * assumption.
    - destruct Hbeh as (u & Hrtc & Hstuck).
      induction Hrtc  as [ | s t ? Hstep Hrtc IH].
      + now constructor.
      + eapply IsSteping.
        * now apply IH.
        * easy.
  Qed.

  Definition does_end s : Prop :=
    ∃ t, P ⊨ s ->>* t ∧ (is_Some (is_final t) ∨ stuck P t).

  Lemma not_ending_diverges:
    ∀ s, ~(does_end s) -> ∀ t, P ⊨ s ->>* t -> diverges t.
  Proof using Type.
    intros s H. unfold diverges.
    coinduction R cih.
    assert (Hs: ∀ t, P ⊨ s ->>* t -> is_final t = None ∧ ~ stuck P t).
    {
      intros t Hstep. apply not_ex_all_not with (n := t) in H.
      split.
      - destruct (is_final t) as [v | ].
        + exfalso. apply H. split; auto.
        + reflexivity.
      - intro Hs. apply H. now auto.
    }
    intros t Hrtc.
    destruct (Hs t) as [Hnfin Hnstuck]; auto.
    unfold stuck in Hnstuck.
    destruct (classic (can_progress P t)) as [Hprog | HnProg].
    - destruct (can_progress_must_step _ _ Hprog) as [u Hstep].
      exists u. split; auto.
      apply cih. eapply rtc_r; eassumption.
    - exfalso. apply Hnstuck. split; auto.
  Qed.

  Theorem every_state_has_beh : ∀ s, ∃ b, b ∈ s.
  Proof using Type.
    intros s. destruct (classic (does_end s)) as [(t & Hrtc & [Hfin | H]) | H].
    - destruct Hfin as [[v m] Hfin].
      exists (Terminating v m). apply has_terminating_behavior.
      exists t; auto.
    - exists Undef. apply has_undef_behavior.
      exists t; auto.
    - exists Diverging. apply has_diverging_behavior.
      apply not_ending_diverges with s; auto.
  Qed.
End Behavior.

Section Refinement.
  Context {Λₜ Λₛ: lang}.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Instance behₜ_elem : ElemOf behavior (state Λₜ) := beh Pₜ.
  Instance behₛ_elem : ElemOf behavior (state Λₛ) := beh Pₛ.

  Variant behavior_order Φ : @behavior Λₜ -> @behavior Λₛ -> Prop :=
  | BehOrderTerm vt vs mt ms :
      Φ (vt, mt) (vs, ms) -> behavior_order Φ (Terminating vt mt) (Terminating vs ms)
  | BehOrderDiv :
      behavior_order Φ Diverging Diverging
  | BehOrderUndef bt :
      behavior_order Φ bt Undef.

  Notation "a '⊑{' Φ '}' b" :=
    (behavior_order Φ a b)
      (at level 70, format "a  '⊑{' Φ '}'  b", no associativity).

  (* A definition of state refinement: *)
  (*    - if the target terminates on (v, m), *)
  (*    the source must either terminate on (v, m) or be stuck. *)
  (*    - if the target diverges, *)
  (*    the source must either diverges or be stuck. *)
  (*    - if the target is stuck, the source should also be stuck. *)
  Definition refines Φ (t: state Λₜ) (s: state Λₛ) : Prop :=
    ∀ b, b ∈ t -> ∃ b', b' ∈ s ∧ b ⊑{Φ} b'.

End Refinement.
