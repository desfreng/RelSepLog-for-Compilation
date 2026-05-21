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

  Notation "t '⟨' iₜ '≲' iₛ '⟩' s '{{' Φ '}}'" :=
    (fsim Wₜ Wₛ Pₜ Pₛ Φ iₜ t iₛ s)
      (at level 70, iₜ at level 69, iₛ at level 69, no associativity).

  Definition StatePair := (state Λₜ * state Λₛ)%type.

  Notation "t '⦉' iₜ ',' wₜ '≲' iₛ ',' wₛ '⦊' s '{{' Φ '}}'" :=
    (gsim Wₜ Wₛ (WfOrdTree StatePair) Pₜ Pₛ Φ iₜ wₜ t iₛ wₛ s)
      (at level 70, iₜ at level 69, iₛ at level 69, no associativity).

  Notation "t '⟪' Rₜ ','  wₜ '≲' Rₛ ',' wₛ '⟫' s '{{' Φ '}}'" :=
    (ealt_sim Rₜ Rₛ Pₜ Pₛ Φ wₜ t wₛ s)
      (at level 70, wₜ at level 69, wₛ at level 69, no associativity).

  Lemma gsim_implies_ealt_sim: ∀ iₜ wₜ t iₛ wₛ s,
    t ⦉ iₜ, wₜ ≲ iₛ, wₛ ⦊ s {{Φ}} ->
    ∃ Rₜ Rₛ zₜ zₛ, t ⟪ Rₜ, zₜ ≲ Rₛ, zₛ ⟫ s {{Φ}}.
  Proof.
    intros iₜ wₜ t iₛ wₛ s Hsim.
    exists (WfLexProd Wₛ _), (WfLexProd Wₜ _), (iₛ, wₜ), (iₜ, wₛ).
    revert iₜ wₜ t iₛ wₛ s Hsim.
    unfold ealt_sim.
    coinduction R cih.
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
      { eassumption. }
      { right. eassumption. }
      apply cih. eassumption.
    - apply EAltTargetSteps.
      { assumption. }
      intros t' Hstep.
      edestruct (IHt _ Hstep) as (iₜ' & wₜ' & Hlt & Hsim & IH).
      eexists. eexists. split.
      { right. eassumption. }
      apply cih. eassumption.
    - apply fsim_implies_gsim in Hsim.
      destruct Hsim as (wₜ' & wₛ' & Hsim).
      eapply IHi in Hsim; try assumption.
      clear cih IHi.
      eapply test.
      eassumption.
      + left. now left.
      + left. now left.
  Qed.
End PROOF.
