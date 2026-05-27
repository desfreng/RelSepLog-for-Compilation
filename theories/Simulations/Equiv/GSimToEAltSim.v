From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Commons.OrdTree.

From RSL Require Import Simulations.Commons.
From RSL Require Import Simulations.FreeSim.

From RSL Require Import Simulations.Equiv.GSim.
From RSL Require Import Simulations.Equiv.EAltSim.
From RSL Require Import Simulations.Equiv.FSimToGSim.

Section PROOF.
  Context {Λₜ Λₛ: lang}.
  Context (Wₜ Wₛ: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Definition StatePair := (state Λₜ * state Λₛ)%type.

  Lemma gsim_implies_ealt_sim: ∀ iₜ wₜ t iₛ wₛ s,
    gsim Wₜ Wₛ (WfOrdTree StatePair) Pₜ Pₛ Φ iₜ wₜ t iₛ wₛ s  ->
    ∃ Rₜ Rₛ zₜ zₛ, ealt_sim Rₜ Rₛ Pₜ Pₛ Φ zₜ t zₛ s.
  Proof using Type.
    intros iₜ wₜ t iₛ wₛ s Hsim.
    exists (WfLexProd Wₛ _), (WfLexProd Wₜ _), (iₛ, wₜ), (iₜ, wₛ).
    revert iₜ wₜ t iₛ wₛ s Hsim.
    unfold ealt_sim. coinduction R cih.
    intros iₜ.
    induction iₜ as [iₜ IHi] using (well_founded_induction wf).
    intros wₜ t iₛ wₛ s Hsim.
    induction Hsim as
      [ iₜ wₜ t iₛ wₛ s Hfin
      | iₜ wₜ t iₛ wₛ s Hstuck
      | iₜ wₜ t iₛ iₛ' wₛ s s' wₛ' Hstep Hlt Hsim IHs
      | iₜ wₜ t iₛ wₛ s Hprogress IHt
      | iₜ iₜ' wₜ t iₛ iₛ' wₛ s Ht Hs Hsim].
    - now constructor.
    - now constructor.
    - eapply EAltSourceSteps.
      + eassumption.
      + right. eassumption.
      + apply cih. eassumption.
    - apply EAltTargetSteps.
      { assumption. }
      intros t' Hstep.
      edestruct (IHt _ Hstep) as (iₜ' & wₜ' & Hlt & Hsim & IH).
      eexists. eexists. split.
      + right. eassumption.
      + apply cih. eassumption.
    - apply fsim_implies_gsim in Hsim.
      destruct Hsim as (wₜ' & wₛ' & Hsim).
      eapply IHi in Hsim.
      + eapply ealt_sim_idx_mono.
        * eassumption.
        * left. now left.
        * left. now left.
      + assumption.
  Qed.
End PROOF.
