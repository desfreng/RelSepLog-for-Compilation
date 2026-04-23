From stdpp Require Import prelude.

From Coinduction Require Import all.

From RSL.Commons Require Import Utils.
From RSL.Commons Require Import Language.

From RSL.Refinement Require Import Behaviors.
From RSL.Refinement Require Import Sim.

(* Set Mangle Names. *)

Section SimSound.
  Context {Λₜ Λₛ: lang}.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Instance behₜ_elem : ElemOf behavior (state Λₜ) := beh Pₜ.
  Instance behₛ_elem : ElemOf behavior (state Λₛ) := beh Pₛ.

  Inductive behavior_order Φ : @behavior Λₜ -> @behavior Λₛ -> Prop :=
  | TerminatingOrder : ∀ (vₜ: value Λₜ) (vₛ: value Λₛ),
    Φ vₜ vₛ -> behavior_order Φ (Terminating vₜ) (Terminating vₛ)
  | DivergingOrder : behavior_order Φ Diverging Diverging
  | UnknownOrder : ∀ s, behavior_order Φ s Unknown.

  Notation "a '⊑{' Φ '}' b" :=
    (behavior_order Φ a b)
      (at level 70, format "a  '⊑{' Φ '}'  b", no associativity).

  Notation "t '≲' s '{{' Φ '}}'" := (gfp (sim_lfp Pₜ Pₛ Φ) t s).

  Lemma terminating_sim Φ : ∀ t s vₜ,
    t ≲ s {{ Φ }} ->
    Terminating vₜ ∈ t ->
    ∃ b, b ∈ s ∧ Terminating vₜ ⊑{Φ} b.
  Proof.
    intros t s vₜ Hsim Hb.
    (* t Terminates -> it reduces to a final state *)
    apply has_terminating_behavior in Hb. destruct Hb as (t' & Hrtc & Hfin).
    revert s Hsim.
    (* Induction on the reduction *)
    induction Hrtc as [ t | t u t' Ht Hrtc IHt ]; intros s Hsim.
    - (* t is final *)
      apply sim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s Hstuck
                        | t s s' Hs _ IHs
                        | t s Hprogress _
                        | t s Hprogress _ ].
      + (* Both Final *)
        destruct Hfinal as (? & vₛ & Ht & ? & ?).
        (* s is final too *)
        inv Ht. exists (Terminating vₛ). now do 2 constructor.
      + (* Source Stuck *)
        exists Unknown. split; now constructor.
      + (* Target Stutter, use IH on s *)
        destruct (IHs Hfin) as (b & Hbeh & Horder).
        exists b. split; auto.
        eapply IsSteping; now eauto.
      + (* Source Stutter -> contradiction *) mixin.
      + (* Both Steps -> contradiction *) mixin.
    - (* t steps *)
      apply sim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s Hstuck
                        | t s s' Hs _ IHs
                        | t s Hprogress Hsim
                        | t s Hprogress Hgfp ].
      + (* Both Final -> contradiction *)
        destruct Hfinal as (? & ? & ? & ? & ?). mixin.
      + (* Source Stuck *)
        exists Unknown. split; now constructor.
      + (* Target Stutter, use IH on s *)
        destruct (IHs Ht) as (b & Hbeh & Horder).
        exists b. split; auto.
        eapply IsSteping; now eauto.
      + (* Source Stutter, use IH on t *)
        apply IHt; auto. apply sim_roll. auto.
      + (* Both Steps, use IH on t*)
        destruct (Hgfp _ Ht) as (s' & Hs & Hsim).
        apply IHt in Hsim; auto.
        destruct Hsim as (b & Hbeh & ?).
        exists b. split; auto.
        eapply IsSteping; eauto.
  Qed.

  Lemma sim_lfp_progress Φ : ∀ t s,
    t ≲ s {{ Φ }} ->
    diverges Pₜ t ->
    stuck Pₛ s ∨
      ∃ s', Pₛ ⊨ s ->> s' ∧
            (
              (∃ t', t' ≲ s' {{ Φ }} ∧ diverges Pₜ t') ∨
                (t ≲ s' {{ Φ }} ∧ diverges Pₜ t)
            ).
  Proof.
    intros t s Hsim Hdiv.
    apply sim_unroll in Hsim.
    induction Hsim as [ t s Hfin
                      | t s Hstuck
                      | t s s' Hstep Hsim' IH
                      | t s Hprog Hsteps IH
                      | t s Hprog Hsteps ].
    - (* BothFinal: Contradiction *)
      destruct Hfin as (vₜ & vₛ & Ht_fin & Hs_fin & HPhi).
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & _).
      mixin.
    - (* SourceStuck *)
      left. exact Hstuck.
    - (* TargetStutter *)
      apply sim_roll in Hsim'.
      right. exists s'. split; now auto.
    - (* TargetSteps *)
      (* t can progress, target waits. Because t diverges, it steps to t' *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & Hdiv_t').
      (* Apply the IH for t' *)
      destruct (IH t' Ht_step Hdiv_t') as
        [Hstuck | (s' & Hstep & [(? & ? & ?) | []])].
      + now left.
      + right. eexists. split; eauto.
      + right. eexists. split; eauto.

    - (* BothSteps *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & Hdiv_t').
      destruct (Hsteps t' Ht_step) as (s' & Hs_step & Hsim_next).
      right. exists s'. split; auto.
      left. exists t'. split; auto.
  Qed.

  Lemma diverging_sim (EM: EM) Φ : ∀ t s,
    t ≲ s {{ Φ }} ->
    Diverging ∈ t ->
    ∃ b, b ∈ s ∧ Diverging ⊑{Φ} b.
  Proof.
    intros t s Hsim Hdiv.
    destruct (EM (∃ s', Pₛ ⊨ s ->>* s' ∧ stuck Pₛ s')) as [Hstuck | Hnstuck].
    - exists Unknown. split; now apply has_stuck_behavior || constructor.
    - exists Diverging. split; try constructor.
      apply has_diverging_behavior in Hdiv.
      assert (H: sim Pₜ Pₛ Φ t s) by exact Hsim. clear Hsim.
      unfold diverges.
      revert t s Hdiv H Hnstuck. coinduction R cih.
      intros t s Hdiv Hsim Hnstuck.
      destruct (sim_lfp_progress _ _ _ Hsim Hdiv) as
        [Hstuck | (s' & Hstep & [(t' & ? & ?) | []])].
      + exfalso. apply Hnstuck. exists s. split; auto.
      + exists s'. split; auto. apply cih with t'; auto.
        intros (s'' & ? & ? ).
        apply Hnstuck. exists s''. split; auto.
        econstructor; now eauto.
      + exists s'. split; auto. apply cih with t; auto.
        intros (s'' & ? & ? ).
        apply Hnstuck. exists s''. split; auto.
        econstructor; now eauto.
  Qed.

  Lemma stuck_sim Φ : ∀ t s,
    t ≲ s {{ Φ }} ->
    Unknown ∈ t ->
    Unknown ∈ s.
  Proof.
    intros t s Hsim Hb.
    (* t reach a stuck state. *)
    apply has_stuck_behavior in Hb. destruct Hb as (t' & Hrtc & Hstuck).
    revert s Hsim.
    (* Induction on the reduction *)
    induction Hrtc as [ t | t u t' Ht Hrtc IHt ]; intros s Hsim.
    - (* t = t' *)
      apply sim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s ?
                        | t s s' Hs _ IHs
                        | t s Hprogress _
                        | t s Hprogress _ ].
      + (* Both Final -> contradiction *)
        destruct Hfinal as (? & vₛ & Ht & ? & ?).
        mixin.
      + (* Source Stuck -> trivial *)
        now constructor.
      + (* Target Stutter, use IH on s *)
        eapply IsSteping; eauto.
        now apply IHs.
      + (* Source Stutter -> contradiction *) mixin.
      + (* Both Steps -> contradiction *) mixin.
    - (* t steps *)
      apply sim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s ?
                        | t s s' Hs _ IHs
                        | t s Hprogress Hsim
                        | t s Hprogress Hgfp ].
      + (* Both Final -> contradiction *)
        destruct Hfinal as (? & ? & ? & ? & ?). mixin.
      + (* Source Stuck -> trivial *)
        now constructor.
      + (* Target Stutter, use IH on s *)
        eapply IsSteping; eauto.
        now apply IHs.
      + (* Source Stutter, use IH on t *)
        apply IHt; auto. apply sim_roll. auto.
      + (* Both Steps, use IH on t *)
        destruct (Hgfp _ Ht) as (s' & Hs & Hsim).
        apply IHt in Hsim; auto.
        eapply IsSteping; now eauto.
  Qed.

  (* A definition of state refinement: *)
  (*    - if the target terminates on (v, m), *)
  (*    the source must either terminate on (v, m) or be stuck. *)
  (*    - if the target diverges, *)
  (*    the source must either diverges or be stuck. *)
  (*    - if the target is stuck, the source should also be stuck. *)
  Definition refines Φ (t: state Λₜ) (s: state Λₛ) :=
    ∀ b, b ∈ t -> ∃ b', b' ∈ s ∧ b ⊑{Φ} b'.

  Theorem sim_sound (EM: EM) Φ : ∀ t s,
    t ≲ s {{ Φ }} -> refines Φ t s.
  Proof.
    intros t s Hsim [] Hb.
    - now apply terminating_sim with t.
    - now apply diverging_sim with t.
    - exists Unknown. split.
      + now apply stuck_sim with (t := t) (Φ := Φ).
      + now constructor.
  Qed.
End SimSound.
