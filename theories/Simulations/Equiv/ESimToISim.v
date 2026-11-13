From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations Require Export Explicit Implicit.

Section PROOF.
  Context {Λt Λs: lang}.
  Context (Et: genv Λt) (Es: genv Λs).
  Context (ϕ: post Λt Λs).

  Lemma esim_implies_isim {W: WfRel} i t s :
    esim W Et Es ϕ i t s ->
    isim Et Es ϕ t s.
  Proof using Type.
    revert i t s.
    unfold isim.
    coinduction C cih.
    intros i.
    induction i as [i IH] using (well_founded_induction wf).
    intros t s Hsim%esim_unroll.
    induction Hsim as [ ? t s Hfinal
                      | ? t s Hstuck
                      | ? i' t s s' Hstep H IHs
                      | ? t s Hprogress H
                      | ? t s Hprogress H ].
    - (* Both Final *)
      now constructor.
    - (* Source Stuck *)
      now constructor.
    - (* Source Steps *)
      apply ISourceSteps with s'.
      { assumption. }
      now apply IH with i'.
    - (* Target Steps *)
      apply ITargetSteps.
      { assumption. }
      intros t' Hstep.
      destruct (H _ Hstep) as (i' & ? & ?).
      now apply IH with i'.
    - (* Both steps *)
      apply IBothSteps.
      { assumption. }
      intros t' Hstep.
      destruct (H _ Hstep) as (i' & s' & Hstep_s & Hsim).
      exists s'. split; auto.
      eapply cih.
      eassumption.
  Qed.
End PROOF.
