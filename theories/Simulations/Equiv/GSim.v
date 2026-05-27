From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.Commons.
From RSL Require Import Simulations.FreeSim.

Section GSimDef.
  Context {Λₜ Λₛ: lang}.
  Context (Wₜ Wₛ W: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Unset Elimination Schemes.

  Inductive gsim : Wₜ -> W -> state Λₜ -> Wₛ -> W -> state Λₛ -> Prop :=
  | GBothFinal : ∀ iₜ wₜ t iₛ wₛ s,
    is_final Φ t s -> gsim iₜ wₜ t iₛ wₛ s

  | GSourceStuck : ∀ iₜ wₜ t iₛ wₛ s,
    stuck Pₛ s -> gsim iₜ wₜ t iₛ wₛ s

  | GSourceSteps : ∀ iₜ wₜ t iₛ iₛ' wₛ s s' wₛ',
    Pₛ ⊨ s ->> s' ->
    wₛ' ⊏ wₛ ->
    gsim iₜ wₜ t iₛ' wₛ' s' ->
    gsim iₜ wₜ t iₛ wₛ s

  | GTargetSteps : ∀ iₜ wₜ t iₛ wₛ s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ iₜ' wₜ',
         wₜ' ⊏ wₜ ∧ gsim iₜ' wₜ' t' iₛ wₛ s) ->
    gsim iₜ wₜ t iₛ wₛ s

  | GProgress : ∀ iₜ iₜ' wₜ t iₛ iₛ' wₛ s,
    iₜ' ⊏ iₜ ->
    iₛ' ⊏ iₛ ->
    fsim Wₜ Wₛ Pₜ Pₛ Φ iₜ' t iₛ' s ->
    gsim iₜ wₜ t iₛ wₛ s.

  Set Elimination Schemes.

  Section GSimInd.
    Variable P : Wₜ -> W -> state Λₜ -> Wₛ -> W -> state Λₛ -> Prop.

    Hypothesis HFinal:
      ∀ iₜ wₜ t iₛ wₛ s, is_final Φ t s -> P iₜ wₜ t iₛ wₛ s.

    Hypothesis HStuck:
      ∀ iₜ wₜ t iₛ wₛ s, stuck Pₛ s -> P iₜ wₜ t iₛ wₛ s.

    Hypothesis HSourceSteps:
      ∀ iₜ wₜ t iₛ iₛ' wₛ s s' wₛ',
      Pₛ ⊨ s ->> s' ->
      wₛ' ⊏ wₛ ->
      gsim iₜ wₜ t iₛ' wₛ' s' ->
      P iₜ wₜ t iₛ' wₛ' s' ->
      P iₜ wₜ t iₛ wₛ s.

    Hypothesis HTargetSteps:
      ∀ iₜ wₜ t iₛ wₛ s,
      can_progress Pₜ t ->
      (∀ t', Pₜ ⊨ t ->> t' ->
             ∃ iₜ' wₜ',
               wₜ' ⊏ wₜ ∧
               gsim iₜ' wₜ' t' iₛ wₛ s ∧
               P iₜ' wₜ' t' iₛ wₛ s) ->
      P iₜ wₜ t iₛ wₛ s.

    Hypothesis HProgress:
      ∀ iₜ iₜ' wₜ t iₛ iₛ' wₛ s,
      iₜ' ⊏ iₜ ->
      iₛ' ⊏ iₛ ->
      fsim Wₜ Wₛ Pₜ Pₛ Φ iₜ' t iₛ' s ->
      P iₜ wₜ t iₛ wₛ s.

    Lemma gsim_ind: ∀ iₜ wₜ t iₛ wₛ s,
      gsim iₜ wₜ t iₛ wₛ s -> P iₜ wₜ t iₛ wₛ s.
    Proof using HFinal HProgress HSourceSteps HStuck HTargetSteps.
      fix IH 7. intros iₜ wₜ t iₛ wₛ s Hsim.
      destruct Hsim as
        [ iₜ wₜ t iₛ wₛ s Hfin
        | iₜ wₜ t iₛ wₛ s Hstuck
        | iₜ wₜ t iₛ wₛ s s' wₛ' Hstep HR Hsim
        | iₜ wₜ t iₛ wₛ s Hprogress Ht
        | iₜ iₜ' wₜ t iₛ iₛ' wₛ s Ht Hs Hgfp ].
      - apply HFinal. assumption.
      - apply HStuck. assumption.
      - eapply HSourceSteps; now eauto.
      - apply HTargetSteps.
        { assumption. }
        intros t' Hstep.
        destruct (Ht _ Hstep) as (iₜ' & wₜ' & HR & Hsim).
        do 2 eexists. now eauto.
      - eapply HProgress; now eauto.
    Qed.
  End GSimInd.

  Register Scheme gsim_ind as ind_nodep for gsim.

  Lemma gsim_weaken_t: ∀ iₜ wₜ t iₛ wₛ s,
    gsim iₜ wₜ t iₛ wₛ s ->
    ∀ w, wₜ ⊑ w ->
    gsim iₜ w t iₛ wₛ s.
  Proof using Type.
    intros iₜ wₜ t iₛ wₛ s Hsim w Hle.
    induction Hsim as
      [ iₜ wₜ t iₛ wₛ s Hfin
      | iₜ wₜ t iₛ wₛ s Hstuck
      | iₜ wₜ t iₛ iₛ' wₛ s s' wₛ' Hstep HR Hsim IHs
      | iₜ wₜ t iₛ wₛ s Hprogress IHt
      | iₜ iₜ' wₜ t iₛ iₛ' wₛ s Ht Hs Hgfp]
      in w, Hle |- *.
    - now constructor.
    - now constructor.
    - eapply GSourceSteps.
      + eassumption.
      + eassumption.
      + now apply IHs.
    - apply GTargetSteps.
      { assumption. }
      intros t' Hstep.
      destruct (IHt _ Hstep) as (iₜ' & wₜ' & Hlt' & Hsim & IH).
      destruct Hle as [ Hlt | -> ].
      + do 2 eexists. split.
        * eassumption.
        * apply IH. now left.
      + do 2 eexists. split; eauto.
    - eapply GProgress; try eassumption.
  Qed.

  Lemma gsim_weaken_s: ∀ iₜ wₜ t iₛ wₛ s,
    gsim iₜ wₜ t iₛ wₛ s ->
    ∀ w, wₛ ⊑ w ->
    gsim iₜ wₜ t iₛ w s.
  Proof using Type.
    intros iₜ wₜ t iₛ wₛ s Hsim w Hle.
    induction Hsim as
      [ iₜ wₜ t iₛ wₛ s Hfin
      | iₜ wₜ t iₛ wₛ s Hstuck
      | iₜ wₜ t iₛ iₛ' wₛ s s' wₛ' Hstep HR Hsim IHs
      | iₜ wₜ t iₛ wₛ s Hprogress IHt
      | iₜ iₜ' wₜ t iₛ iₛ' wₛ s Ht Hs Hgfp]
      in w, Hle |- *.
    - now constructor.
    - now constructor.
    - destruct Hle as [ Hlt | -> ].
      + eapply GSourceSteps.
        * eassumption.
        * eassumption.
        * apply IHs. now left.
      + eapply GSourceSteps.
        * eassumption.
        * eassumption.
        * apply IHs. now right.
    - apply GTargetSteps.
      { assumption. }
      intros t' Hstep.
      destruct (IHt _ Hstep) as (iₜ' & wₜ' & Hlt' & Hsim & IH).
      do 2 eexists. split.
      + eassumption.
      + apply IH. assumption.
    - eapply GProgress; try eassumption.
  Qed.
End GSimDef.
