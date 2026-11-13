From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations Require Export LockStep.
From RSL.Language Require Export Behaviors.

From Stdlib Require Import Classical.


Section LSimSound.
  Context {Λt Λs: lang}.
  Context (Et: genv Λt) (Es: genv Λs).

  Instance beht_elem : ElemOf behavior (config Λt) := beh Et.
  Instance behs_elem : ElemOf behavior (config Λs) := beh Es.

  Notation "a '⊑{' ϕ '}' b" :=
    (behavior_order ϕ a b)
      (at level 70, format "a  '⊑{' ϕ '}'  b", no associativity).

  Notation "t '≲' s '{{' ϕ '}}'" :=
    (lsim Et Es ϕ t s)
      (at level 1, no associativity).

  Lemma terminating_lsim ϕ t s:
    t ≲ s {{ ϕ }} ->
    ∀ vt mt,
    Terminating vt mt ∈ t ->
    ∃ b, b ∈ s ∧ Terminating vt mt ⊑{ϕ} b.
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
                        | t s s' Hs Hstuck
                        | t s Hprogress Hboth ].
      + (* Both Final *)
        destruct Hfinal as (? & vs & ? & ms & Ht & ? & ?).
        (* s is final too *)
        inv Ht. exists (Terminating vs ms). by do 2 constructor.
      + exists Undef. split.
        * apply has_undef_behavior. exists s'. by auto using super_stuck_is_stuck.
        * by constructor.
      + (* Both Steps -> contradiction *)
        langmixin.
    - (* t steps *)
      intros s Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply lsim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s s' Hs Hstuck
                        | t s Hprogress IHboth ].
      + (* Both Final -> contradiction *)
        langmixin.
      + exists Undef. split.
        * apply has_undef_behavior. exists s'. by auto using super_stuck_is_stuck.
        * by constructor.
      + (* Both Steps, use IH on t *)
        destruct (IHboth _ Ht) as (s' & Hs & Hgfp).
        edestruct IHt as (b & Hbeh & ?); eauto.
        exists b. split; auto.
        eapply IsSteping; now eauto.
  Qed.

  Lemma lsim_lfp_progress ϕ t s:
    t ≲ s {{ ϕ }} ->
    diverges Et t ->
    (∃ s', Es ⊨ s ->>* s' ∧ stuck Es s')
    ∨ (∃ t' s', Es ⊨ s ->> s' ∧ t' ≲ s' {{ ϕ }} ∧ diverges Et t').
  Proof using Type.
    intros Hsim Hdiv.
    (* Induction on the least-fixpoint of the relation *)
    apply lsim_unroll in Hsim.
    induction Hsim as [ t s Hfinal
                      | t s s' Hs Hfinal
                      | t s Hprogress IHboth ].
    - (* Both Final: Contradiction *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & _).
      langmixin.
    - left. eexists. by eauto using super_stuck_is_stuck.
    - (* Both Steps *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & Hdiv_t').
      (* Use IH on t to make s steps *)
      destruct (IHboth t' Ht_step) as (s' & Hstep & Hgfp).
      right. exists t', s'. now auto.
  Qed.

  Lemma diverging_lsim ϕ t s:
    t ≲ s {{ ϕ }} ->
    Diverging ∈ t ->
    ∃ b, b ∈ s ∧ Diverging ⊑{ϕ} b.
  Proof using Type.
    intros Hsim Hdiv.
    destruct (classic (∃ s', Es ⊨ s ->>* s' ∧ stuck Es s')) as [Hstuck | Hnstuck].
    - exists Undef. split; last by constructor.
      by eapply has_undef_behavior.
    - exists Diverging. split; constructor.
      apply has_diverging_behavior in Hdiv.
      (* We prove by coinduction that s diverges *)
      unfold diverges.
      revert t s Hdiv Hsim Hnstuck. coinduction ξ cih.
      intros t s Hdiv Hsim Hnstuck.
      (* [sim_lfp_progress] give us s' such that s ->> s' *)
      destruct (lsim_lfp_progress _ _ _ Hsim Hdiv) as [Hs | Hprog].
      + by exfalso.
      + destruct Hprog as (t' & s' & Hstep & Hsim' & Hdiv').
        (* s steps *)
        exists s'. split; auto. eapply cih; eauto.
        intros (s'' & ? & ? ).
        apply Hnstuck. exists s''. split; auto.
        econstructor; now eauto.
  Qed.

  Lemma undef_lsim ϕ t s:
    t ≲ s {{ ϕ }} ->
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
                        | t s s' Hs Hstuck_s
                        | t s Hprogress _ ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Both Steps -> contradiction *)
        apply has_undef_behavior. exists s'. by auto using super_stuck_is_stuck.
      + langmixin.
    - (* t steps *)
      intros s Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply lsim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s s' Hstuck_s
                        | t s Hprogress Hboth ].
      + (* Both Final -> contradiction *)
        langmixin.
      + apply has_undef_behavior. exists s'. by auto using super_stuck_is_stuck.
      + (* Both Steps, use IH on t *)
        destruct (Hboth _ Htstep) as (s' & Hstep & Hgfp).
        apply IHt in Hgfp; auto.
        eapply IsSteping; now eauto.
  Qed.

  Theorem lsim_sound ϕ t s:
    t ≲ s {{ ϕ }} -> flex_refines Et Es ϕ t s.
  Proof using Type.
    intros Hsim [] Hb.
    - eapply terminating_lsim; now eauto.
    - eapply diverging_lsim; now eauto.
    - exists Undef. split.
      + eapply undef_lsim; now eauto.
      + now constructor.
  Qed.
End LSimSound.
