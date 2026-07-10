From RSL Require Import Prelude.

From Stdlib Require Import Classical.
From Coinduction Require Import all.

From RSL Require Import Commons.Behaviors.
From RSL Require Import Simulations.FreeSim.

Section FSimSound.
  Context {Λₜ Λₛ: lang}.
  Context {J I: WfRel}.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Instance behₜ_elem : ElemOf behavior (state Λₜ) := beh Pₜ.
  Instance behₛ_elem : ElemOf behavior (state Λₛ) := beh Pₛ.

  Notation "a '⊑{' Φ '}' b" :=
    (behavior_order Φ a b)
      (at level 70, format "a  '⊑{' Φ '}'  b", no associativity).

  Notation " t '<{' j ',' i '}=' s '{{' Φ '}}'" :=
    (fsim J I Pₜ Pₛ Φ t j i s)
      (at level 1, i at level 0, j at level 0, no associativity).

  Lemma terminating_fsim Φ t j i s:
    t <{ j, i }= s {{ Φ }} ->
    ∀ vt mt,
    Terminating vt mt ∈ t ->
    ∃ b, b ∈ s ∧ Terminating vt mt ⊑{Φ} b.
  Proof using Type.
    intros Hsim vt mt Hb.
    (* t Terminates -> it reduces to a final state *)
    apply has_terminating_behavior in Hb. destruct Hb as (t' & Hrtc & Hfin).
    (* Induction on the reduction *)
    revert j i s Hsim.
    induction Hrtc as [ t | t u t' Hstep Hrtc IHrtc ]; intros j.
    - (* t is final *)
      (* Induction on the progress index of t *)
      induction j as [j IHi] using (well_founded_induction wf).
      intros s i Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply fsim_unroll in Hsim.
      induction Hsim as [ t j i s Hfinal
                        | t j i s Hstuck
                        | t j i i' s s' Hs ? IHs
                        | t j i s Hprogress IHt
                        | t j j' i i' s Hprogress ? Hgfp ].
      + (* Both Final *)
        destruct Hfinal as (? & [vs ms] & Ht & ? & ?).
        (* s is final too *)
        inv Ht. exists (Terminating vs ms). now do 2 constructor.
      + (* Source Stuck *)
        exists Undef. split; now constructor.
      + (* Source Steps, use IH on s *)
        destruct (IHs Hfin) as (b & Hbeh & Horder).
        { intros. edestruct IHi as (b & Hbeh & Horder); now eauto. }
        exists b. split; auto.
        eapply IsSteping; now eauto.
      + (* Target Steps -> contradiction *)
        langmixin.
      + (* Coind -> use IH on progress index *)
        eapply IHi; now eauto.
    - (* t steps *)
      (* Induction on the progress index of t *)
      induction j as [j IHi] using (well_founded_induction wf).
      intros s i Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply fsim_unroll in Hsim.
      induction Hsim as [ t j i s Hfinal
                        | t j i s Hstuck
                        | t j i i' s s' Hs ? IHs
                        | t j i s Hprogress IHt
                        | t j j' i i' s Hprogress ? Hgfp ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Source Stuck *)
        exists Undef. split; now constructor.
      + (* Source Steps, use IH on s *)
        destruct (IHs Hstep) as (b & Hbeh & Horder).
        { intros. edestruct IHi as (b & Hbeh & Horder); now eauto. }
        exists b. split; auto.
        eapply IsSteping; now eauto.
      + (* Target Steps, use IH on t *)
        edestruct (IHt _ Hstep) as (j' & Hsim & IH).
        eapply IHrtc; auto. apply fsim_roll.
        now apply Hsim.
      + (* Coinductive case -> use IH on progress index *)
        edestruct IHi as (b & Hbeh & Horder); now eauto.
  Qed.

  Lemma fsim_lfp_progress Φ t j s i:
    t <{ j, i }= s {{ Φ }} ->
    diverges Pₜ t ->
    stuck Pₛ s ∨
      ∃ t' j' s' i',
        Pₛ ⊨ s ->> s' ∧
        diverges Pₜ t' ∧
        t' <{ j', i' }= s' {{ Φ }}.
  Proof using Type.
    (* Induction on the progress index of s *)
    revert t j.
    induction i as [i IHi] using (well_founded_induction wf).
    intros t j Hsim Hdiv.
    (* Induction on the least-fixpoint of the relation *)
    apply fsim_unroll in Hsim.
    induction Hsim as [ t j i s Hfinal
                      | t j i s Hstuck
                      | t j i i' s s' Hs Hsim IHs
                      | t j i s Hprogress IHt
                      | t j j' i i' s Hprogress ? Hgfp ].
    - (* BothFinal: Contradiction *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Hstep & _).
      langmixin.
    - (* SourceStuck *)
      left. exact Hstuck.
    - (* Source Steps *)
      apply fsim_roll in Hsim.
      right. repeat econstructor; now eauto.
    - (* Target Steps *)
      (* t can progress, source waits. Because t diverges, it steps to t' *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Hstep & Hdiv').
      (* Apply the IH for t' *)
      edestruct (IHt _ Hstep) as (j' & Hsim & IH).
      edestruct IH as [ Hstuck | (? & ? & s' & i' & Hs' & Hdiv & Hsim')];
        try eassumption.
      + now left.
      + right. repeat econstructor; now eauto.
    - (* Coinductive case *)
      edestruct IHi as [Hstuck | (? & ? & s' & ? & Hs' & Hdiv' & Hsim')];
        try eassumption.
      + now left.
      + right. repeat econstructor; now eauto.
  Qed.

  Lemma diverging_fsim Φ t j s i:
    t <{ j, i }= s {{ Φ }} ->
    Diverging ∈ t ->
    ∃ b, b ∈ s ∧ Diverging ⊑{Φ} b.
  Proof using Type.
    intros Hsim Hdiv.
    (* We see in the future: can s be stuck ? *)
    destruct (classic (∃ s', Pₛ ⊨ s ->>* s' ∧ stuck Pₛ s')) as [Hstuck | Hnstuck].
    - (* s can be stuck -> s has Undef behavior *)
      exists Undef. split; now apply has_undef_behavior || constructor.
    - (* s is never stuck -> s is diverging *)
      exists Diverging. split; try constructor.
      apply has_diverging_behavior in Hdiv.
      (* We prove by coinduction that s diverges *)
      unfold diverges.
      revert t j s i Hdiv Hsim Hnstuck.
      coinduction R cih.
      intros t j s i Hdiv Hsim Hnstuck.
      (* [sim_lfp_progress] give us s' such that s ->> s' *)
      destruct (fsim_lfp_progress _ _ _ _ _ Hsim Hdiv) as
        [Hstuck | (? & j' & s' & i' & Hs' & ? & ?)].
      + (* s is stuck -> contradiction *)
        exfalso. apply Hnstuck. exists s. split; eauto.
      + (* s steps *)
        exists s'. split; auto. eapply cih; eauto.
        intros (s'' & ? & ? ).
        apply Hnstuck. exists s''. split; auto.
        econstructor; now eauto.
  Qed.

  Lemma undef_fsim Φ t j s i:
    t <{ j, i }= s {{ Φ }} ->
    Undef ∈ t ->
    Undef ∈ s.
  Proof using Type.
    intros Hsim Hb.
    (* t reach a stuck state. *)
    apply has_undef_behavior in Hb. destruct Hb as (t' & Hrtc & Hstuck).
    (* Induction on the reduction *)
    revert j i s Hsim.
    induction Hrtc as [ t | t u t' Hstep Hrtc IHrtc ]; intros j.
    - (* t = t' *)
      (* Induction on the progress index of t *)
      induction j as [j IHi] using (well_founded_induction wf).
      intros s i Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply fsim_unroll in Hsim.
      induction Hsim as [ t j i s Hfinal
                        | t j i s Hsstuck
                        | t j i i' s s' Hs ? IHs
                        | t j i s Hprogress IHt
                        | t j j' i i' s Hprogress ? Hgfp ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Source Stuck -> trivial *)
        now constructor.
      + (* Source Steps, use IH on s *)
        eapply IsSteping; eauto.
        now apply IHs.
      + (* Target Steps -> contradiction *)
        langmixin.
      + (* Coinductive case, use IH on progress index *)
        eapply IHi; now eauto.
    - (* t steps *)
      (* Induction on the progress index of t *)
      induction j as [j IHi] using (well_founded_induction wf).
      intros s i Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply fsim_unroll in Hsim.
      induction Hsim as [ t j i s Hfinal
                        | t j i s Hsstuck
                        | t j i i' s s' Hs ? IHs
                        | t j i s Hprogress IHt
                        | t j j' i i' s Hprogress ? Hgfp ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Source Stuck -> trivial *)
        now constructor.
      + (* Source Steps, use IH on s *)
        eapply IsSteping; eauto.
        apply IHs; auto.
      + (* Target Steps, use IH on t *)
        edestruct (IHt _ Hstep) as (j' & Hsim & IH).
        eapply IHrtc; eauto.
        apply fsim_roll.
        now apply Hsim.
      + (* Both Steps, use IH on t *)
        eapply IHi; now eauto.
  Qed.

  Theorem fsim_sound Φ t j s i:
    t <{ j, i }= s {{ Φ }} ->
    refines Pₜ Pₛ Φ t s.
  Proof using Type.
    intros Hsim [] Hb.
    - eapply terminating_fsim; now eauto.
    - eapply diverging_fsim; now eauto.
    - exists Undef. split.
      + eapply undef_fsim; now eauto.
      + now constructor.
  Qed.
End FSimSound.
