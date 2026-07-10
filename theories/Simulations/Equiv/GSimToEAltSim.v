From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Commons.OrdTree.

From RSL Require Import Simulations.FreeSim.

From RSL Require Import Simulations.Equiv.GSim.
From RSL Require Import Simulations.Equiv.EAltSim.
From RSL Require Import Simulations.Equiv.FSimToGSim.

Section PROOF.
  Context {Λₜ Λₛ: lang}.
  Context (J I: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).
  Context (Φ: value Λₜ * memory -> value Λₛ * memory -> Prop).

  Definition StatePair := (state Λₜ * state Λₛ)%type.

  Lemma gsim_implies_ealt_sim: ∀ j b t i a s,
    gsim J I (WfOrdTree StatePair) Pₜ Pₛ Φ j b t i a s  ->
    ∃ Rₜ Rₛ zₜ zₛ, ealt_sim Rₜ Rₛ Pₜ Pₛ Φ zₜ t zₛ s.
  Proof using Type.
    intros j b t i a s Hsim.
    exists (WfLexProd I _), (WfLexProd J _), (i, b), (j, a).
    revert j b t i a s Hsim.
    unfold ealt_sim. coinduction R cih.
    intros j.
    induction j as [j IHi] using (well_founded_induction wf).
    intros b t i a s Hsim.
    induction Hsim as
      [ j b t i a s Hfin
      | j b t i a s Hstuck
      | j b t i i' a s s' a' Hstep Hlt Hsim IHs
      | j b t i a s Hprogress IHt
      | j j' b t i i' a s Ht Hs Hsim].
    - now constructor.
    - now constructor.
    - eapply EAltSourceSteps.
      + eassumption.
      + right. eassumption.
      + apply cih. eassumption.
    - apply EAltTargetSteps.
      { assumption. }
      intros t' Hstep.
      edestruct (IHt _ Hstep) as (j' & b' & Hlt & Hsim & IH).
      eexists. eexists. split.
      + right. eassumption.
      + apply cih. eassumption.
    - apply fsim_implies_gsim in Hsim.
      destruct Hsim as (b' & a' & Hsim).
      eapply IHi in Hsim.
      + eapply ealt_sim_idx_mono.
        * eassumption.
        * left. now left.
        * left. now left.
      + assumption.
  Qed.
End PROOF.
