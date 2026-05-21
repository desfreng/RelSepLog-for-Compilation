From RSL Require Import Prelude.

From Stdlib Require Import Classical.
From Coinduction Require Import all.

From RSL Require Import Simulations.Commons.
From RSL Require Import Simulations.Behaviors.
From RSL Require Import Simulations.FreeSim.

(* Set Mangle Names. *)

Section FSimSound.
  Context {Λₜ Λₛ: lang}.
  Context {Wₜ Wₛ: WfRel}.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Instance behₜ_elem : ElemOf behavior (state Λₜ) := beh Pₜ.
  Instance behₛ_elem : ElemOf behavior (state Λₛ) := beh Pₛ.

  Notation "a '⊑{' Φ '}' b" :=
    (behavior_order Φ a b)
      (at level 70, format "a  '⊑{' Φ '}'  b", no associativity).

  Notation "'⟨' t ',' it '⟩' '≲' '⟨' s ',' is '⟩' '{{' Φ '}}'" :=
    (fsim Wₜ Wₛ Pₜ Pₛ Φ it t is s)
      (at level 70, no associativity).

  Lemma terminating_fsim Φ : ∀ t iₜ s iₛ vₜ,
    ⟨t, iₜ⟩ ≲ ⟨s, iₛ⟩ {{ Φ }} ->
    Terminating vₜ ∈ t ->
    ∃ b, b ∈ s ∧ Terminating vₜ ⊑{Φ} b.
  Proof.
    intros t iₜ s iₛ vₜ Hsim Hb.
    (* t Terminates -> it reduces to a final state *)
    apply has_terminating_behavior in Hb. destruct Hb as (t' & Hrtc & Hfin).
    (* Induction on the reduction *)
    revert iₜ iₛ s Hsim.
    induction Hrtc as [ t | t u t' Hstep Hrtc IHrtc ]; intros iₜ.
    - (* t is final *)
      (* Induction on the progress index of t *)
      induction iₜ as [iₜ IHi] using (well_founded_induction wf).
      intros s iₛ Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply fsim_unroll in Hsim.
      induction Hsim as [ iₜ t iₛ s Hfinal
                        | iₜ t iₛ s Hstuck
                        | iₜ t iₛ iₛ' s s' Hs ? IHs
                        | iₜ t iₛ s Hprogress IHt
                        | iₜ iₜ' t iₛ iₛ' s Hprogress ? Hgfp ].
      + (* Both Final *)
        destruct Hfinal as (? & vₛ & Ht & ? & ?).
        (* s is final too *)
        inv Ht. exists (Terminating vₛ). now do 2 constructor.
      + (* Source Stuck *)
        exists Undef. split; now constructor.
      + (* Source Steps, use IH on s *)
        destruct (IHs Hfin) as (b & Hbeh & Horder).
        { intros. edestruct IHi as (b & Hbeh & Horder); now eauto. }
        exists b. split; auto.
        eapply IsSteping; now eauto.
      + (* Target Steps -> contradiction *)
        mixin.
      + (* Coind -> use IH on progress index *)
        eapply IHi; now eauto.
    - (* t steps *)
      (* Induction on the progress index of t *)
      induction iₜ as [iₜ IHi] using (well_founded_induction wf).
      intros s iₛ Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply fsim_unroll in Hsim.
      induction Hsim as [ iₜ t iₛ s Hfinal
                        | iₜ t iₛ s Hstuck
                        | iₜ t iₛ iₛ' s s' Hs ? IHs
                        | iₜ t iₛ s Hprogress IHt
                        | iₜ iₜ' t iₛ iₛ' s Hprogress ? Hgfp ].
      + (* Both Final -> contradiction *)
        destruct Hfinal as (? & ? & ? & ? & ?). mixin.
      + (* Source Stuck *)
        exists Undef. split; now constructor.
      + (* Source Steps, use IH on s *)
        destruct (IHs Hstep) as (b & Hbeh & Horder).
        { intros. edestruct IHi as (b & Hbeh & Horder); now eauto. }
        exists b. split; auto.
        eapply IsSteping; now eauto.
      + (* Target Steps, use IH on t *)
        edestruct (IHt _ Hstep) as (iₜ' & Hsim & IH).
        eapply IHrtc; auto. apply fsim_roll.
        now apply Hsim.
      + (* Coinductive case -> use IH on progress index *)
        edestruct IHi as (b & Hbeh & Horder); now eauto.
  Qed.

  Lemma fsim_lfp_progress Φ : ∀ t iₜ s iₛ,
    ⟨t, iₜ⟩ ≲ ⟨s, iₛ⟩ {{ Φ }} ->
    diverges Pₜ t ->
    stuck Pₛ s ∨
      ∃ t' iₜ' s' iₛ',
        Pₛ ⊨ s ->> s' ∧
        diverges Pₜ t' ∧
        ⟨t', iₜ'⟩ ≲ ⟨s', iₛ'⟩ {{ Φ }}.
  Proof.
    intros t iₜ s iₛ.
    (* Induction on the progress index of s *)
    revert t iₜ.
    induction iₛ as [iₛ IHi] using (well_founded_induction wf).
    intros t iₜ Hsim Hdiv.
    (* Induction on the least-fixpoint of the relation *)
    apply fsim_unroll in Hsim.
    induction Hsim as [ iₜ t iₛ s Hfinal
                      | iₜ t iₛ s Hstuck
                      | iₜ t iₛ iₛ' s s' Hs ? IHs
                      | iₜ t iₛ s Hprogress IHt
                      | iₜ iₜ' t iₛ iₛ' s Hprogress ? Hgfp ].
    - (* BothFinal: Contradiction *)
      destruct Hfinal as (vₜ & vₛ & Ht_fin & Hs_fin & HPhi).
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Hstep & _).
      mixin.
    - (* SourceStuck *)
      left. exact Hstuck.
    - (* Source Steps *)
      apply fsim_roll in Hsim.
      right. repeat econstructor; now eauto.
    - (* Target Steps *)
      (* t can progress, source waits. Because t diverges, it steps to t' *)
      apply diverges_unroll in Hdiv. destruct Hdiv as (t' & Hstep & Hdiv').
      (* Apply the IH for t' *)
      edestruct (IHt _ Hstep) as (iₜ' & Hsim & IH).
      edestruct IH as [ Hstuck | (? & ? & s' & iₛ' & Hs' & Hdiv & Hsim')];
        try eassumption.
      + now left.
      + right. repeat econstructor; now eauto.
    - (* Coinductive case *)
      edestruct IHi as [Hstuck | (? & ? & s' & ? & Hs' & Hdiv' & Hsim')];
        try eassumption.
      + now left.
      + right. repeat econstructor; now eauto.
  Qed.

  Lemma diverging_fsim Φ : ∀ t iₜ s iₛ,
    ⟨t, iₜ⟩ ≲ ⟨s, iₛ⟩ {{ Φ }} ->
    Diverging ∈ t ->
    ∃ b, b ∈ s ∧ Diverging ⊑{Φ} b.
  Proof.
    intros t iₜ s iₛ Hsim Hdiv.
    (* We see in the future: can s be stuck ? *)
    destruct (classic (∃ s', Pₛ ⊨ s ->>* s' ∧ stuck Pₛ s')) as [Hstuck | Hnstuck].
    - (* s can be stuck -> s has Undef behavior *)
      exists Undef. split; now apply has_undef_behavior || constructor.
    - (* s is never stuck -> s is diverging *)
      exists Diverging. split; try constructor.
      apply has_diverging_behavior in Hdiv.
      (* We prove by coinduction that s diverges *)
      unfold diverges.
      revert t iₜ s iₛ Hdiv Hsim Hnstuck.
      coinduction R cih.
      intros t iₜ s iₛ Hdiv Hsim Hnstuck.
      (* [sim_lfp_progress] give us s' such that s ->> s' *)
      destruct (fsim_lfp_progress _ _ _ _ _ Hsim Hdiv) as
        [Hstuck | (? & iₜ' & s' & iₛ' & Hs' & ? & ?)].
      + (* s is stuck -> contradiction *)
        exfalso. apply Hnstuck. exists s. split; eauto.
      + (* s steps *)
        exists s'. split; auto. eapply cih; eauto.
        intros (s'' & ? & ? ).
        apply Hnstuck. exists s''. split; auto.
        econstructor; now eauto.
  Qed.

  Lemma undef_fsim Φ : ∀ t iₜ s iₛ,
    ⟨t, iₜ⟩ ≲ ⟨s, iₛ⟩ {{ Φ }} ->
    Undef ∈ t ->
    Undef ∈ s.
  Proof.
    intros t iₜ s iₛ Hsim Hb.
    (* t reach a stuck state. *)
    apply has_undef_behavior in Hb. destruct Hb as (t' & Hrtc & Hstuck).
    (* Induction on the reduction *)
    revert iₜ iₛ s Hsim.
    induction Hrtc as [ t | t u t' Hstep Hrtc IHrtc ]; intros iₜ.
    - (* t = t' *)
      (* Induction on the progress index of t *)
      induction iₜ as [iₜ IHi] using (well_founded_induction wf).
      intros s iₛ Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply fsim_unroll in Hsim.
      induction Hsim as [ iₜ t iₛ s Hfinal
                        | iₜ t iₛ s Hsstuck
                        | iₜ t iₛ iₛ' s s' Hs ? IHs
                        | iₜ t iₛ s Hprogress IHt
                        | iₜ iₜ' t iₛ iₛ' s Hprogress ? Hgfp ].
      + (* Both Final -> contradiction *)
        destruct Hfinal as (? & vₛ & Ht & ? & ?).
        mixin.
      + (* Source Stuck -> trivial *)
        now constructor.
      + (* Source Steps, use IH on s *)
        eapply IsSteping; eauto.
        now apply IHs.
      + (* Target Steps -> contradiction *)
        mixin.
      + (* Coinductive case, use IH on progress index *)
        eapply IHi; now eauto.
    - (* t steps *)
      (* Induction on the progress index of t *)
      induction iₜ as [iₜ IHi] using (well_founded_induction wf).
      intros s iₛ Hsim.
      (* Induction on the least-fixpoint of the relation *)
      apply fsim_unroll in Hsim.
      induction Hsim as [ iₜ t iₛ s Hfinal
                        | iₜ t iₛ s Hsstuck
                        | iₜ t iₛ iₛ' s s' Hs ? IHs
                        | iₜ t iₛ s Hprogress IHt
                        | iₜ iₜ' t iₛ iₛ' s Hprogress ? Hgfp ].
      + (* Both Final -> contradiction *)
        destruct Hfinal as (? & ? & ? & ? & ?). mixin.
      + (* Source Stuck -> trivial *)
        now constructor.
      + (* Source Steps, use IH on s *)
        eapply IsSteping; eauto.
        apply IHs; auto.
      + (* Target Steps, use IH on t *)
        edestruct (IHt _ Hstep) as (iₜ' & Hsim & IH).
        eapply IHrtc; eauto.
        apply fsim_roll.
        now apply Hsim.
      + (* Both Steps, use IH on t *)
        eapply IHi; now eauto.
  Qed.

  Theorem fsim_sound Φ : ∀ t iₜ s iₛ,
    ⟨t, iₜ⟩ ≲ ⟨s, iₛ⟩ {{ Φ }} -> refines Pₜ Pₛ Φ t s.
  Proof.
    intros t iₜ s iₛ Hsim [] Hb.
    - eapply terminating_fsim; now eauto.
    - eapply diverging_fsim; now eauto.
    - exists Undef. split.
      + eapply undef_fsim; now eauto.
      + now constructor.
  Qed.
End FSimSound.
