From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations Require Export Implicit Free.

Section PROOF.
  Context {Λt Λs: lang}.
  Context (Et: genv Λt) (Es: genv Λs).
  Context (ϕ: post Λt Λs).

  Lemma isim_implies_fsim {J I: WfRel} :
    ∀ t s,
    isim Et Es ϕ t s ->
    ∀ (j Tj: J) (i Ti: I),
    j ⊏ Tj ->
    i ⊏ Ti ->
    fsim _ _ Et Es ϕ t j i s.
  Proof using Type.
    unfold fsim.
    coinduction R cih.
    intros t s Hsim.
    apply isim_unroll in Hsim.
    induction Hsim as [ t s Hfinal
                      | t s Hstuck
                      | t s s' Hstep Hs IHs
                      | t s Hprogress Ht IHt
                      | t s Hprogress Hboth ];
      intros j Tj i Ti Hj Hi.
    - (* Both Final *)
      now constructor.
    - (* Source Stuck *)
      now constructor.
    - (* Source Steps *)
      eapply FSourceSteps.
      + eassumption.
      + eapply IHs; eassumption.
    - (* Target Steps *)
      apply FTargetSteps.
      + assumption.
      + intros t' Hstep. eexists.
        eapply IHt; eassumption.
    - (* Both steps *)
      apply FTargetSteps; try assumption.
      intros t' Hstep.
      destruct (Hboth _ Hstep) as (s' & Hstep_s & Hsim).
      eexists.
      eapply FSourceSteps; try eassumption.
      eapply FProgress; try eassumption.
      eapply cih; eassumption.
  Qed.

End PROOF.
