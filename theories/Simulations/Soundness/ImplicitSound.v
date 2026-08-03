From RSL Require Import Prelude.

From Stdlib Require Import Classical.
From Coinduction Require Import all.

From RSL Require Import Commons.Behaviors.
From RSL Require Import Simulations.ImplicitSim.

Section ISimSound.
  Context {Λt Λs: lang}.
  Context (Pt: prog Λt) (Ps: prog Λs).

  Instance behₜ_elem : ElemOf behavior (state Λt) := beh Pt.
  Instance behₛ_elem : ElemOf behavior (state Λs) := beh Ps.

  Notation "a '⊑{' Φ '}' b" :=
    (behavior_order Φ a b)
      (at level 70, format "a  '⊑{' Φ '}'  b", no associativity).

  Notation "t '≲' s '{{' Φ '}}'" :=
    (isim Pt Ps Φ t s)
      (at level 1, no associativity).

  Lemma terminating_isim Φ t s:
    t ≲ s {{ Φ }} ->
    ∀ vt mt,
    Terminating vt mt ∈ t ->
    ∃ b, b ∈ s ∧ Terminating vt mt ⊑{Φ} b.
  Proof using Type.
    intros Hsim vt mt Hb.
    (* t Terminates -> it reduces to a final state *)
    apply has_terminating_behavior in Hb. destruct Hb as (t' & Hrtc & Hfin).
    revert s Hsim.
    (* Induction on the reduction *)
    induction Hrtc as [ t | t u t' Ht Hrtc IHt ]; intros s Hsim.
    - (* t is final *)
      apply isim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s Hstuck
                        | t s s' Hs _ IHs
                        | t s Hprogress _
                        | t s Hprogress _ ].
      + (* Both Final *)
        destruct Hfinal as (? & [vs ms] & Ht & ? & ?).
        (* s is final too *)
        inv Ht. exists (Terminating vs ms). now do 2 constructor.
      + (* Source Stuck *)
        exists Undef. split; now constructor.
      + (* Source Steps, use IH on s *)
        destruct (IHs Hfin) as (b & Hbeh & Horder).
        exists b. split; auto.
        eapply IsSteping; now eauto.
      + (* Target Steps -> contradiction *)
        langmixin.
      + (* Both Steps -> contradiction *)
        langmixin.
    - (* t steps *)
      apply isim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s Hstuck
                        | t s s' Hs _ IHs
                        | t s Hprogress Hsim
                        | t s Hprogress Hgfp ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Source Stuck *)
        exists Undef. split; now constructor.
      + (* Source Steps, use IH on s *)
        destruct (IHs Ht) as (b & Hbeh & Horder).
        exists b. split; auto.
        eapply IsSteping; now eauto.
      + (* Target Steps, use IH on t *)
        apply IHt; auto. apply isim_roll. auto.
      + (* Both Steps, use IH on t *)
        destruct (Hgfp _ Ht) as (s' & Hs & Hsim).
        apply IHt in Hsim; auto.
        destruct Hsim as (b & Hbeh & ?).
        exists b. split; auto.
        eapply IsSteping; eauto.
  Qed.

  Lemma isim_lfp_progress Φ t s:
    t ≲ s {{ Φ }} ->
    diverges Pt t ->
    stuck Ps s ∨
      ∃ t' s', Ps ⊨ s ->> s' ∧ t' ≲ s' {{ Φ }} ∧ diverges Pt t'.
  Proof using Type.
    intros Hsim Hdiv.
    (* Induction on the least-fixpoint of the relation *)
    apply isim_unroll in Hsim.
    induction Hsim as [ t s Hfin
                      | t s Hstuck
                      | t s s' Hstep Hsim' IH
                      | t s Hprog Hsteps IH
                      | t s Hprog Hsteps ].
    - (* BothFinal: Contradiction *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & _).
      langmixin.
    - (* SourceStuck *)
      left. exact Hstuck.
    - (* Source Steps *)
      apply isim_roll in Hsim'.
      right. exists t, s'. split; now auto.
    - (* Target Steps *)
      (* t can progress, source waits. Because t diverges, it steps to t' *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & Hdiv_t').
      (* Apply the IH for t' *)
      destruct (IH t' Ht_step Hdiv_t') as
        [Hstuck | (u & s' & Hstep & Hsim & Hdiv')].
      + now left.
      + right. repeat econstructor. all: now eauto.
    - (* Both Steps *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & Hdiv_t').
      destruct (Hsteps t' Ht_step) as (s' & Hs_step & Hsim_next).
      right. exists t', s'. split; auto.
  Qed.

  Lemma diverging_isim Φ t s:
    t ≲ s {{ Φ }} ->
    Diverging ∈ t ->
    ∃ b, b ∈ s ∧ Diverging ⊑{Φ} b.
  Proof using Type.
    intros Hsim Hdiv.
    (* We see in the future: can s be stuck ? *)
    destruct (classic (∃ s', Ps ⊨ s ->>* s' ∧ stuck Ps s')) as [Hstuck | Hnstuck].
    - (* s can be stuck -> s has Undef behavior *)
      exists Undef. split; now apply has_undef_behavior || constructor.
    - (* s is never stuck -> s is diverging *)
      exists Diverging. split; try constructor.
      apply has_diverging_behavior in Hdiv.
      assert (H: isim _ _ _ _ _) by exact Hsim. clear Hsim.
      (* We prove by coinduction that s diverges *)
      unfold diverges.
      revert t s Hdiv H Hnstuck. coinduction R cih.
      intros t s Hdiv Hsim Hnstuck.
      (* [sim_lfp_progress] give us s' such that s ->> s' *)
      destruct (isim_lfp_progress _ _ _ Hsim Hdiv) as
        [Hstuck | (t' & s' & Hstep & Hsim' & Hdiv')].
      + (* s is stuck -> contradiction *)
        exfalso. apply Hnstuck. exists s. split; auto.
      + (* s steps and t too *)
        exists s'. split; auto. apply cih with t'; auto.
        intros (s'' & ? & ? ).
        apply Hnstuck. exists s''. split; auto.
        econstructor; now eauto.
  Qed.

  Lemma undef_isim Φ t s:
    t ≲ s {{ Φ }} ->
    Undef ∈ t ->
    Undef ∈ s.
  Proof using Type.
    intros Hsim Hb.
    (* t reach a stuck state. *)
    apply has_undef_behavior in Hb. destruct Hb as (t' & Hrtc & Hstuck).
    revert s Hsim.
    (* Induction on the reduction *)
    induction Hrtc as [ t | t u t' Ht Hrtc IHt ]; intros s Hsim.
    - (* t = t' *)
      apply isim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s ?
                        | t s s' Hs _ IHs
                        | t s Hprogress _
                        | t s Hprogress _ ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Source Stuck -> trivial *)
        now constructor.
      + (* Target Stutter, use IH on s *)
        eapply IsSteping; eauto.
        now apply IHs.
      + (* Source Stutter -> contradiction *)
        langmixin.
      + (* Both Steps -> contradiction *)
        langmixin.
    - (* t steps *)
      apply isim_unroll in Hsim.
      induction Hsim as [ t s Hfinal
                        | t s ?
                        | t s s' Hs _ IHs
                        | t s Hprogress Hsim
                        | t s Hprogress Hgfp ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Source Stuck -> trivial *)
        now constructor.
      + (* Target Stutter, use IH on s *)
        eapply IsSteping; eauto.
        now apply IHs.
      + (* Source Stutter, use IH on t *)
        apply IHt; auto. apply isim_roll. auto.
      + (* Both Steps, use IH on t *)
        destruct (Hgfp _ Ht) as (s' & Hs & Hsim).
        apply IHt in Hsim; auto.
        eapply IsSteping; now eauto.
  Qed.

  Theorem isim_sound Φ t s:
    t ≲ s {{ Φ }} -> refines Pt Ps Φ t s.
  Proof using Type.
    intros Hsim [] Hb.
    - now apply terminating_isim with t.
    - now apply diverging_isim with t.
    - exists Undef. split.
      + now apply undef_isim with (t := t) (Φ := Φ).
      + now constructor.
  Qed.
End ISimSound.
