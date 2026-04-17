From stdpp Require Import prelude.

From Coinduction Require Import all.

From RSL Require Import RTL.
From RSL Require Import Semantics.
From RSL Require Import SemanticsSpec.
From RSL Require Import Refinement.
From RSL Require Import Sim.

Section Adequacy.
  Context (P: program).
  Context {Φ: observation} `{!PreOrder Φ}.

  Notation "t '≲' s '{{' Φ '}}'" := (gfp (sim_lfp P Φ) t s).

  Local Instance beh_elem : ElemOf behavior state := λ b s, beh P s b.
  Local Instance beh_subset_eq : SqSubsetEq behavior := @behavior_order Φ.

  Lemma sim_unroll t s :
    t ≲ s {{ Φ }} -> sim_lfp' P Φ (gfp (sim_lfp P Φ)) t s.
  Proof.
    intros H. now apply (gfp_pfp (sim_lfp _ _)).
  Qed.

  Lemma converging_sim : ∀ (t s: state) v m,
    t ≲ s {{ Φ }} ->
    Terminating v m ∈ t ->
    ∃ b, b ∈ s ∧ Terminating v m ⊑ b.
  Proof.
    intros t s v m Hsim Hb.
    erewrite -> (@has_terminating_behavior P) in Hb by eassumption.
    destruct Hb as (t' & Hrtc & Hfin).
    pose proof (final_to_final _ _ _ Hfin) as Hf.
    revert s Hsim.
    induction Hrtc as [ t' | t t' t'' Hstep Hrtc IH ].
    - intros s Hsim.
      apply sim_unroll in Hsim.
      induction Hsim; subst.
      + inv H. inv Hfin. exists vₛ, mₛ. now repeat constructor.
      + exfalso. eapply final_not_stuck; eassumption.
      + destruct (IHHsim Hfin Hf) as (v' & m' & Ht' & HΦ).
        eexists. eexists. split.
        * eapply IsSteping. apply Ht'. assumption.
        * apply HΦ.
      + exfalso. eapply final_no_progress; eassumption.
      + exfalso. eapply final_no_progress; eassumption.
    - intros s Hsim.
      apply sim_unroll in Hsim.
      induction Hsim; subst.
      + inv H. inv Hstep.
      + exfalso. destruct H as [Hs _].
        apply Hs. eexists. eassumption.
      + destruct (IHHsim Hstep) as (v' & m' & Hs' & HΦ).
        eexists. eexists. split.
        * eapply IsSteping. apply Hs'. assumption.
        * apply HΦ.
      + apply (IH Hfin Hf).
        step.
        apply H0. assumption.
      + destruct (H0 _ Hstep) as (s' & Hs' & HΦ).
        apply (IH Hfin Hf) in HΦ. destruct HΦ as (v' & m' & Hterm & HΦ).
        eexists. eexists. split.
        * eapply IsSteping; eauto.
        * apply HΦ.
  Qed.
End Adequacy.
