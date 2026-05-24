From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.Commons.
From RSL Require Import Simulations.ImplicitSim.
From RSL Require Import Simulations.ExplicitSim.
From RSL Require Import Simulations.FreeSim.

From RSL Require Import Simulations.Equiv.FSimToGSim.
From RSL Require Import Simulations.Equiv.GSimToEAltSim.
From RSL Require Import Simulations.Equiv.EAltSimToESimLax.
From RSL Require Import Simulations.Equiv.ESimLaxToESim.

(* Set Mangle Names. *)

Section SimEquiv.
  Context {Λₜ Λₛ: lang}.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Notation "t '≲' s '{{' Φ '}}'" :=
    (isim Pₜ Pₛ Φ t s)
      (at level 70, no associativity).

  Notation "t '≲' '[' i ']' s '{{' Φ '}}'" :=
    (esim _ Pₜ Pₛ Φ i t s)
      (at level 70, no associativity).

  Notation "t '⟨' iₜ '≲' iₛ '⟩' s '{{' Φ '}}'" :=
    (fsim _ _ Pₜ Pₛ Φ iₜ t iₛ s)
      (at level 70, iₜ at level 69, iₛ at level 69, no associativity).

  Lemma isim_to_fsim {Wₜ Wₛ: WfRel} Φ :
    ∀ t s,
    t ≲ s {{ Φ }} ->
    ∀ (iₜ iₜ': Wₜ) (iₛ iₛ': Wₛ),
    iₜ ⊏ iₜ' ->
    iₛ ⊏ iₛ' ->
    t ⟨iₜ ≲ iₛ⟩ s {{ Φ }}.
  Proof using.
    unfold fsim.
    coinduction R cih.
    intros t s Hsim.
    apply isim_unroll in Hsim.
    induction Hsim as [ t s Hfinal
                      | t s Hstuck
                      | t s s' Hstep Hs IHs
                      | t s Hprogress Ht IHt
                      | t s Hprogress Hboth ];
      intros iₜ iₜ' iₛ iₛ' HRt HRs.
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
      eapply FProgress.
      { eassumption. }
      { eassumption. }
      eapply cih.
      + apply Hsim.
      + eassumption.
      + eassumption.
  Qed.

  Lemma esim_to_isim {W: WfRel} Φ :
    ∀ (i: W) t s,
    t ≲[i] s {{ Φ }} ->
    t ≲ s {{ Φ }}.
  Proof using.
    unfold isim.
    coinduction ξ cih.
    intros i.
    induction i as [i IH] using (well_founded_induction wf).
    intros t s Hsim.
    apply esim_unroll in Hsim.
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

  Lemma fsim_to_esim {Wₜ Wₛ: WfRel} Φ:
    ∀ (iₜ: Wₜ) t (iₛ: Wₛ) s,
    t ⟨iₜ ≲ iₛ⟩ s {{ Φ }} ->
    ∃ (W: WfRel) (i: W), t ≲[i] s {{ Φ }}.
  Proof using.
    intros iₜ t iₛ s Hsim.
    apply fsim_implies_gsim in Hsim.
    destruct Hsim as (wₜ & wₛ & Hgsim).
    apply gsim_implies_ealt_sim in Hgsim.
    destruct Hgsim as (Rₜ & Rₛ & zₜ & zₛ & Healtsim).
    apply ealt_sim_implies_esim_lax in Healtsim.
    destruct Healtsim as (W & i & Hesimlax).
    apply esim_lax_implies_esim in Hesimlax.
    destruct Hesimlax as (R & w & Hesim).
    do 2 eexists. eassumption.
  Qed.

  Lemma index_irrel {Wₜ Wₛ: WfRel} Φ:
    ∀ t s,
    (∃ (iₜ: Wₜ) (iₛ: Wₛ), t ⟨iₜ ≲ iₛ⟩ s {{ Φ }}) ->
    ∀ iₜ iₛ,
    (∃ T : Wₜ, iₜ ⊏ T) ->
    (∃ T : Wₛ, iₛ ⊏ T) ->
    t ⟨iₜ ≲ iₛ⟩ s {{ Φ }}.
  Proof using.
    intros t s (oₜ & oₛ & Hsim) iₜ iₛ (Tₜ & Ht) (Tₛ & Hs).
    apply fsim_to_esim in Hsim.
    destruct Hsim as (W & i & Hesim).
    eapply isim_to_fsim.
    - eapply esim_to_isim. eassumption.
    - eassumption.
    - eassumption.
  Qed.

  (* en supposant que soit ⊤ soit pas ⊤ dans Wₜ et Wₛ *)
End SimEquiv.
