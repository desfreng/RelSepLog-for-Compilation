From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Commons Require Import OrdTree.

From RSL.Simulations Require Export ExplicitAlt.
From RSL.Simulations.Equiv Require Export FSimToGSim.

Section PROOF.
  Context {Λt Λs: lang}.
  Context (J I: WfRel).
  Context (Et: genv Λt) (Es: genv Λs).
  Context (ϕ: post Λt Λs).

  Definition StatePair := (config Λt * config Λs)%type.

  Lemma gsim_implies_ealt_sim: ∀ j b t i a s,
    gsim J I (WfOrdTree StatePair) Et Es ϕ j b t i a s  ->
    ealt_sim _ _ Et Es ϕ (ord_pair i b) t (ord_pair j a) s.
  Proof using Type.
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
    - eapply EAltSourceSteps with (i' := ord_pair _ _).
      + eassumption.
      + right. eassumption.
      + apply cih. eassumption.
    - apply EAltTargetSteps.
      { assumption. }
      intros t' Hstep.
      edestruct (IHt _ Hstep) as (j' & b' & Hlt & Hsim & IH).
      eexists (ord_pair _ _). eexists. split.
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
