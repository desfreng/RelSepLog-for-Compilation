From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations Require Export Explicit.
From RSL.Language Require Export Behaviors.

From Stdlib Require Import Classical.

Section ESimSound.
  Context {Λt Λs: lang}.
  Context (W: WfRel) (Et: genv Λt) (Es: genv Λs).

  Instance beht_elem : ElemOf behavior (config Λt) := beh Et.
  Instance behs_elem : ElemOf behavior (config Λs) := beh Es.

  Notation "a '⊑{' ϕ '}' b" :=
    (behavior_order ϕ a b)
      (at level 70, format "a  '⊑{' ϕ '}'  b", no associativity).

  Notation "t '≲' '[' i ']' s '{{' ϕ '}}'" :=
    (esim W Et Es ϕ i t s)
      (at level 1, no associativity).

  Lemma terminating_esim ϕ i t s:
    t ≲[i] s {{ ϕ }} ->
    ∀ vt mt,
    Terminating vt mt ∈ t ->
    ∃ b, b ∈ s ∧ Terminating vt mt ⊑{ϕ} b.
  Proof using Type.
    intros Hsim vt mt Hb.
    (* t Terminates -> it reduces to a final config *)
    apply has_terminating_behavior in Hb. destruct Hb as (t' & Hrtc & Hfin).
    revert i s Hsim.
    (* Induction on the reduction *)
    induction Hrtc as [ t | t u t' Ht Hrtc IHt ]; intros i.
    - (* t is final *)
      (* Induction on the stuttering index *)
      induction i as [i IHi] using (well_founded_induction wf).
      intros s Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply esim_unroll in Hsim.
      induction Hsim as [ i t s Hfinal
                        | i t s Hstuck
                        | i i' t s s' Hs Hlt Hgfp
                        | i t s Hprogress Ht
                        | i t s Hprogress Ht ].
      + (* Both Final *)
        destruct Hfinal as (? & vs & ? & ms & Ht & ? & ?).
        (* s is final too *)
        inv Ht. exists (Terminating vs ms). now do 2 constructor.
      + (* Source Stuck *)
        exists Undef. split; constructor. now apply super_stuck_is_stuck.
      + (* Source Steps, use IH on stuttering index *)
        destruct (IHi _ Hlt _ Hgfp) as (b & Hbeh & Horder).
        exists b. split; auto.
        eapply IsSteping; now eauto.
      + (* Target Steps -> contradiction *)
        langmixin.
      + (* Both Steps -> contradiction *)
        langmixin.
    - (* t steps *)
      (* Induction on the stuttering index *)
      induction i as [i IHi] using (well_founded_induction wf).
      intros s Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply esim_unroll in Hsim.
      induction Hsim as [ i t s Hfinal
                        | i t s Hstuck
                        | i i' t s s' Hs Hlt Hgfp
                        | i t s Hprogress IH
                        | i t s Hprogress IH ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Source Stuck *)
        exists Undef. split; constructor. now apply super_stuck_is_stuck.
      + (* Source Steps, use IH on stuttering index *)
        destruct (IHi _ Hlt _ Hgfp) as (b & Hbeh & Horder).
        exists b. split; auto.
        eapply IsSteping; now eauto.
      + (* Target Steps, use IH on t *)
        destruct (IH _ Ht) as (i' & Hlt & Hgfp).
        apply IHt with i'; now auto.
      + (* Both Steps, use IH on t *)
        destruct (IH _ Ht) as (i' & s' & Hs & Hgfp).
        edestruct IHt as (b & Hbeh & ?); eauto.
        exists b. split; auto.
        eapply IsSteping; now eauto.
  Qed.

  Lemma esim_lfp_progress ϕ i t s:
    t ≲[i] s {{ ϕ }} ->
    diverges Et t ->
    stuck Es s ∨
      ∃ i' t' s', Es ⊨ s ->> s' ∧ t' ≲[i'] s' {{ ϕ }} ∧ diverges Et t'.
  Proof using Type.
    revert t s.
    (* Induction on the progress index *)
    induction i as [i IHi] using (well_founded_induction wf).
    intros t s Hsim Hdiv.
    (* Induction on the least-fixpoint of the relation *)
    apply esim_unroll in Hsim.
    induction Hsim as [ i t s Hfinal
                      | i t s Hstuck
                      | i i' t s s' Hs Hlt Hgfp
                      | i t s Hprogress IHt
                      | i t s Hprogress IHt ].
    - (* Both Final: Contradiction *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & _).
      langmixin.
    - (* Source Stuck *)
      left. now apply super_stuck_is_stuck.
    - (* Source Steps *)
      right. exists i', t, s'. now auto.
    - (* Target Steps *)
      (* t can progress, source waits. Because t diverges, it steps to t' *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & Hdiv_t').
      (* Use IHt to lower progress index *)
      destruct (IHt t' Ht_step) as (i' & Hlt & Hgfp).
      (* Use IHi on new progress index *)
      destruct (IHi _ Hlt _ _ Hgfp); now auto.
    - (* Both Steps *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Ht_step & Hdiv_t').
      (* Use IH on t to make s steps *)
      destruct (IHt t' Ht_step) as (i' & s' & Hstep & Hgfp).
      right. exists i', t', s'. now auto.
  Qed.

  Lemma diverging_esim ϕ i t s:
    t ≲[i] s {{ ϕ }} ->
    Diverging ∈ t ->
    ∃ b, b ∈ s ∧ Diverging ⊑{ϕ} b.
  Proof using Type.
    intros Hsim Hdiv.
    (* We see in the future: can s be stuck ? *)
    destruct (classic (∃ s', Es ⊨ s ->>* s' ∧ stuck Es s')) as [Hstuck | Hnstuck].
    - (* s can be stuck -> s has Undef behavior *)
      exists Undef. split; now apply has_undef_behavior || constructor.
    - (* s is never stuck -> s is diverging *)
      exists Diverging. split; try constructor.
      apply has_diverging_behavior in Hdiv.
      (* We prove by coinduction that s diverges *)
      unfold diverges.
      revert i t s Hdiv Hsim Hnstuck. coinduction ξ cih.
      intros i t s Hdiv Hsim Hnstuck.
      (* [sim_lfp_progress] give us s' such that s ->> s' *)
      destruct (esim_lfp_progress _ _ _ _ Hsim Hdiv) as
        [Hstuck | (i' & t' & s' & Hstep & Hsim' & Hdiv')].
      + (* s is stuck -> contradiction *)
        exfalso. apply Hnstuck. exists s. split; auto.
      + (* s steps *)
        exists s'. split; auto. eapply cih; eauto.
        intros (s'' & ? & ? ).
        apply Hnstuck. exists s''. split; auto.
        econstructor; now eauto.
  Qed.

  Lemma undef_esim ϕ i t s:
    t ≲[i] s {{ ϕ }} ->
    Undef ∈ t ->
    Undef ∈ s.
  Proof using Type.
    intros Hsim Hb.
    (* t reach a stuck state. *)
    apply has_undef_behavior in Hb. destruct Hb as (t' & Hrtc & Hstuck).
    revert i s Hsim.
    (* Induction on the reduction *)
    induction Hrtc as [ t | t u t' Htstep Hrtc IHt ]; intros i.
    - (* t = t' *)
      (* Induction on the stuttering index *)
      induction i as [i IHi] using (well_founded_induction wf).
      intros s Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply esim_unroll in Hsim.
      induction Hsim as [ i t s Hfinal
                        | i t s Hstucks
                        | i i' t s s' Hs Hlt Hgfp
                        | i t s Hprogress _
                        | i t s Hprogress _ ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Source Stuck -> trivial *)
        constructor. now apply super_stuck_is_stuck.
      + (* Source Steps, use IH on progress index *)
        eapply IsSteping; eauto.
        eapply IHi; now eauto.
      + (* Target Steps -> contradiction *)
        langmixin.
      + (* Both Steps -> contradiction *)
        langmixin.
    - (* t steps *)
      (* Induction on the stuttering index *)
      induction i as [i IHi] using (well_founded_induction wf).
      intros s Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply esim_unroll in Hsim.
      induction Hsim as [ i t s Hfinal
                        | i t s Hstucks
                        | i i' t s s' Hs Hlt Hgfp
                        | i t s Hprogress Ht
                        | i t s Hprogress Ht ].
      + (* Both Final -> contradiction *)
        langmixin.
      + (* Source Stuck -> trivial *)
        constructor. now apply super_stuck_is_stuck.
      + (* Source Steps, use IH on progress index *)
        eapply IsSteping; eauto.
        eapply IHi; now eauto.
      + (* Target Steps, use IH on t *)
        destruct (Ht _ Htstep) as (i' & _ & Hgfp).
        apply IHt with i'; now auto.
      + (* Both Steps, use IH on t *)
        destruct (Ht _ Htstep) as (i' & s' & Hstep & Hgfp).
        apply IHt in Hgfp; auto.
        eapply IsSteping; now eauto.
  Qed.

  Theorem esim_sound ϕ i t s:
    t ≲[i] s {{ ϕ }} -> flex_refines Et Es ϕ t s.
  Proof using Type.
    intros Hsim [] Hb.
    - eapply terminating_esim; now eauto.
    - eapply diverging_esim; now eauto.
    - exists Undef. split.
      + eapply undef_esim; now eauto.
      + now constructor.
  Qed.
End ESimSound.
