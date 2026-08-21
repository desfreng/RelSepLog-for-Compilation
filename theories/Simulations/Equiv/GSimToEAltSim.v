From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Commons.OrdTree.

From RSL Require Import Simulations.FreeSim.

From RSL Require Import Simulations.Equiv.GSim.
From RSL Require Import Simulations.Equiv.EAltSim.
From RSL Require Import Simulations.Equiv.FSimToGSim.

Section PROOF.
  Context {Λt Λs: lang}.
  Context (J I: WfRel).
  Context (Pt: prog Λt) (Ps: prog Λs).
  Context (Φ: value Λt -> value Λs -> memory -> memory -> Prop).

  Definition StatePair := (config Λt * config Λs)%type.

  Lemma gsim_implies_ealt_sim: ∀ j b t i a s,
    gsim J I (WfOrdTree StatePair) Pt Ps Φ j b t i a s  ->
    ∃ Rₜ Rₛ zₜ zₛ, ealt_sim Rₜ Rₛ Pt Ps Φ zₜ t zₛ s.
  Proof using Type.
    intros j b t i a s Hsim.
    exists (WfLexProd I _), (WfLexProd J _), (ord_pair _ _ i b), (ord_pair _ _ j a).
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
    - eapply EAltSourceSteps with (i' := ord_pair _ _ _ _).
      + eassumption.
      + right. eassumption.
      + apply cih. eassumption.
    - apply EAltTargetSteps.
      { assumption. }
      intros t' Hstep.
      edestruct (IHt _ Hstep) as (j' & b' & Hlt & Hsim & IH).
      eexists (ord_pair _ _ _ _). eexists. split.
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
