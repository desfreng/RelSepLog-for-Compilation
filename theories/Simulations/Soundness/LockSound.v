From RSL Require Import Prelude.

From Stdlib Require Import Classical.
From Coinduction Require Import all.

From RSL Require Import Commons.Behaviors.
From RSL Require Import Simulations.LockStep.

Section LSimSound.
  Context {Λt Λs: lang}.
  Context (Pt: prog Λt) (Ps: prog Λs).

  Instance beht_elem : ElemOf behavior (config Λt) := beh Pt.
  Instance behs_elem : ElemOf behavior (config Λs) := beh Ps.

  Notation "a '≡{' Φ '}' b" :=
    (behavior_equal Φ a b)
      (at level 70, format "a  '≡{' Φ '}'  b", no associativity).

  Notation "t '≲' s '{{' Φ '}}'" :=
    (lsim Pt Ps Φ t s)
      (at level 1, no associativity).

  Lemma terminating_lsim Φ t s:
    t ≲ s {{ Φ }} ->
    ∀ vt mt,
    Terminating vt mt ∈ t ->
    ∃ b, b ∈ s ∧ Terminating vt mt ≡{Φ} b.
  Proof using Type.
    intros Hsim vt mt Hb.
    (* t Terminates -> it reduces to a final config *)
    apply has_terminating_behavior in Hb. destruct Hb as (t' & Hrtc & Hfin).
    revert s Hsim.
    (* Induction on the reduction *)
    induction Hrtc as [ t | t u t' Ht Hrtc IHt ].
    - (* t is final *)
      intros s Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply lsim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s Hprogress Hboth ].
      + (* Both Final *)
        destruct Hfinal as (? & vs & ? & ms & Ht & ? & ?).
        (* s is final too *)
        inv Ht. exists (Terminating vs ms). by do 2 constructor.
      + (* Both Steps -> contradiction *)
        langmixin.
    - (* t steps *)
      intros s Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply lsim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s Hprogress IHboth ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Both Steps, use IH on t *)
        destruct (IHboth _ Ht) as (s' & Hs & Hgfp).
        edestruct IHt as (b & Hbeh & ?); eauto.
        exists b. split; auto.
        eapply IsSteping; now eauto.
  Qed.

  Lemma lsim_lfp_progress Φ t s:
    t ≲ s {{ Φ }} ->
    diverges Pt t ->
    ∃ t' s', Ps ⊨ s ->> s' ∧ t' ≲ s' {{ Φ }} ∧ diverges Pt t'.
  Proof using Type.
    intros Hsim Hdiv.
    (* Induction on the least-fixpoint of the relation *)
    apply lsim_unroll in Hsim.
    induction Hsim as [ t s Hfinal
                      | t s Hprogress IHboth ].
    - (* Both Final: Contradiction *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & _).
      langmixin.
    - (* Both Steps *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & Hdiv_t').
      (* Use IH on t to make s steps *)
      destruct (IHboth t' Ht_step) as (s' & Hstep & Hgfp).
      exists t', s'. now auto.
  Qed.

  Lemma diverging_lsim Φ t s:
    t ≲ s {{ Φ }} ->
    Diverging ∈ t ->
    Diverging ∈ s.
  Proof using Type.
    intros Hsim Hdiv. constructor.
    apply has_diverging_behavior in Hdiv.
    (* We prove by coinduction that s diverges *)
    unfold diverges.
    revert t s Hdiv Hsim. coinduction ξ cih.
    intros t s Hdiv Hsim.
    (* [sim_lfp_progress] give us s' such that s ->> s' *)
    destruct (lsim_lfp_progress _ _ _ Hsim Hdiv) as (t' & s' & Hstep & Hsim' & Hdiv').
    (* s steps *)
    exists s'. split; auto. eapply cih; now eauto.
  Qed.

  Lemma undef_lsim Φ t s:
    t ≲ s {{ Φ }} ->
    Undef ∈ t ->
    Undef ∈ s.
  Proof using Type.
    intros Hsim Hb.
    (* t reach a stuck state. *)
    apply has_undef_behavior in Hb. destruct Hb as (t' & Hrtc & Hstuck).
    revert s Hsim.
    (* Induction on the reduction *)
    induction Hrtc as [ t | t u t' Htstep Hrtc IHt ].
    - (* t = t' *)
      intros s Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply lsim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s Hprogress _ ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Both Steps -> contradiction *)
        langmixin.
    - (* t steps *)
      intros s Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply lsim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s Hprogress Hboth ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Both Steps, use IH on t *)
        destruct (Hboth _ Htstep) as (s' & Hstep & Hgfp).
        apply IHt in Hgfp; auto.
        eapply IsSteping; now eauto.
  Qed.

  Theorem lsim_sound Φ t s:
    t ≲ s {{ Φ }} -> rigid_refines Pt Ps Φ t s.
  Proof using Type.
    intros Hsim [] Hb.
    - eapply terminating_lsim; now eauto.
    - exists Diverging. split.
      + eapply diverging_lsim; now eauto.
      + now constructor.
    - exists Undef. split.
      + eapply undef_lsim; now eauto.
      + now constructor.
  Qed.
End LSimSound.
