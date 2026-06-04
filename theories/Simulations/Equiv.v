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

Section SimEquiv.
  Context {Λₜ Λₛ: lang}.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ → value Λₛ → Prop).

  Abbreviation isim := (isim Pₜ Pₛ Φ).
  Abbreviation esim := (esim _ Pₜ Pₛ Φ).
  Abbreviation fsim := (fsim _ _  Pₜ Pₛ Φ).

  Lemma isim_to_fsim {J I: WfRel} :
    ∀ t s,
    isim t s ->
    ∀ (j Tj: J) (i Ti: I),
    j ⊏ Tj ->
    i ⊏ Ti ->
    fsim j t i s.
  Proof using Type.
    unfold fsim, FreeSim.fsim.
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

  Lemma esim_to_isim {W: WfRel} :
    ∀ (i: W) t s,
    esim i t s ->
    isim t s.
  Proof using Type.
    unfold isim.
    coinduction C cih.
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

  Lemma fsim_to_esim {J I: WfRel}:
    ∀ (j: J) t (i: I) s,
    fsim j t i s ->
    ∃ (W: WfRel) (i: W), esim i t s.
  Proof using Type.
    intros j t i s Hsim.
    apply fsim_implies_gsim in Hsim.
    destruct Hsim as (wt & ws & Hgsim).
    apply gsim_implies_ealt_sim in Hgsim.
    destruct Hgsim as (Rt & Rs & zt & zs & Healtsim).
    apply ealt_sim_implies_esim_lax in Healtsim.
    destruct Healtsim as (W & ? & Hesimlax).
    apply esim_lax_implies_esim in Hesimlax.
    destruct Hesimlax as (R & w & Hesim).
    do 2 eexists. eassumption.
  Qed.

  Lemma index_irrel
    {J J' I I': WfRel} `{NoIsolatedElements J'} `{NoIsolatedElements I'}:
    ∀ (j: J) t (i: I) s,
    fsim j t i s ->
    ∀ (j': J') (i': I'),
    fsim j' t i' s.
  Proof using Type.
    intros j t i s Hsim.
    apply fsim_to_esim in Hsim.
    destruct Hsim as (W & x & Hsim).
    eapply esim_to_isim in Hsim.
    clear W x i j.
    intros j' i'.
    destruct (no_isolated j') as [jj [ Hltj | Hgtj ]];
      destruct (no_isolated i') as [ii [ Hlti | Hlti ]];
      eapply fsim_mono;
      (eapply isim_to_fsim; eassumption) || reflexivity || (left; eassumption).
  Qed.

  Theorem fsim_same_as_bool:
    ∀ (J I: WfRel),
    Inhabited J ->
    Inhabited I ->
    NoIsolatedElements J ->
    NoIsolatedElements I ->
    ∀ t s,
    (∃ (j: J) (i: I), fsim j t i s)
    <->
      (∃ j i : bool, fsim j t i s).
  Proof using Type.
    intros J I HInJ HInI HIsoJ HIsoI t s.
    split; intros (j & i & Hsim).
    - exists true, true.
      eapply index_irrel.
      eassumption.
    - destruct HInJ as [jj].
      destruct HInI as [ii].
      exists jj, ii.
      eapply index_irrel.
      eassumption.
  Qed.
End SimEquiv.
