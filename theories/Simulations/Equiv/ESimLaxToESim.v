From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.Commons.
From RSL Require Import Simulations.ExplicitSim.
From RSL Require Import Simulations.Equiv.ExplicitSimLax.

Section PROOF.
  Context {Λₜ Λₛ: lang}.
  Context (W: WfRel) (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Definition Wnew : WfRel := WfLexProd W WfNat.

  Lemma esim_lax_to_esim_inv: ∀ n i t s s',
    Pₛ ⊨ s -{ n }> s' ->
    esim_lax W Pₜ Pₛ Φ i t s' ->
    esim Wnew Pₜ Pₛ Φ (i, n) t s.
  Proof.
    unfold esim.
    coinduction C cih.
    intros n.
    induction n as [ | n IH ].
    - intros i t s s' Hstep Hsim. inv Hstep.
      apply esim_lax_unroll in Hsim.
      induction Hsim as
        [
        |
        | ? ? ? s s''
        |
        |
        ].
      + now constructor.
      + now constructor.
      + destruct (pstep_to_nstep_l _ _ H) as (n & s' & Hstep & Hnstep).
        eapply ESourceSteps.
        { eassumption. }
        2:{ eapply cih; eassumption. }
        now constructor.
      + apply ETargetSteps.
        { assumption. }
        intros t' Hstep.
        destruct (H0 _ Hstep) as (i' & Hlt & Hsim).
        exists (i', 0).
        split.
        * now constructor.
        * eapply cih; eassumption || constructor.
      + apply EBothSteps.
        { assumption. }
        intros t' Hstep.
        destruct (H0 _ Hstep) as (i' & s'' & Hs & Hsim).
        destruct (pstep_to_nstep_l _ _ Hs) as (n & s' & Hsteps & Hnstep).
        do 2 eexists. split.
        * eassumption.
        * eapply cih; eassumption || constructor.
    - intros i t s s' Hstep Hsim.
      inv Hstep as [ | ? ? ? ? Hs Hnstep ].
      eapply ESourceSteps.
      { eassumption. }
      2:{ eapply cih; eassumption. }
      right. simpl. lia.
  Qed.

  Lemma esim_lax_implies_esim: ∀ i t s,
    esim_lax W Pₜ Pₛ Φ i t s ->
    ∃ (R: WfRel) w, esim R Pₜ Pₛ Φ w t s.
  Proof.
    intros i t s Hsim.
    exists Wnew, (i, 0).
    apply esim_lax_to_esim_inv with s.
    - constructor.
    - assumption.
  Qed.
End PROOF.
