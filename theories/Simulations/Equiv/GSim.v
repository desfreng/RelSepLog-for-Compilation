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
  | GBothFinal : ∀ j b t i a s,
    is_final Φ t s -> gsim j b t i a s

  | GSourceStuck : ∀ j b t i a s,
    stuck Pₛ s -> gsim j b t i a s

  | GSourceSteps : ∀ j b t i i' a s s' a',
    Pₛ ⊨ s ->> s' ->
    a' ⊏ a ->
    gsim j b t i' a' s' ->
    gsim j b t i a s

  | GTargetSteps : ∀ j b t i a s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ j' b',
         b' ⊏ b ∧ gsim j' b' t' i a s) ->
    gsim j b t i a s

  | GProgress : ∀ j j' b t i i' a s,
    j' ⊏ j ->
    i' ⊏ i ->
    fsim Wₜ Wₛ Pₜ Pₛ Φ j' t i' s ->
    gsim j b t i a s.

  Set Elimination Schemes.

  Section GSimInd.
    Variable P : Wₜ -> W -> state Λₜ -> Wₛ -> W -> state Λₛ -> Prop.

    Hypothesis HFinal:
      ∀ j b t i a s, is_final Φ t s -> P j b t i a s.

    Hypothesis HStuck:
      ∀ j b t i a s, stuck Pₛ s -> P j b t i a s.

    Hypothesis HSourceSteps:
      ∀ j b t i i' a s s' a',
      Pₛ ⊨ s ->> s' ->
      a' ⊏ a ->
      gsim j b t i' a' s' ->
      P j b t i' a' s' ->
      P j b t i a s.

    Hypothesis HTargetSteps:
      ∀ j b t i a s,
      can_progress Pₜ t ->
      (∀ t', Pₜ ⊨ t ->> t' ->
             ∃ j' b',
               b' ⊏ b ∧
               gsim j' b' t' i a s ∧
               P j' b' t' i a s) ->
      P j b t i a s.

    Hypothesis HProgress:
      ∀ j j' b t i i' a s,
      j' ⊏ j ->
      i' ⊏ i ->
      fsim Wₜ Wₛ Pₜ Pₛ Φ j' t i' s ->
      P j b t i a s.

    Lemma gsim_ind: ∀ j b t i a s,
      gsim j b t i a s -> P j b t i a s.
    Proof using HFinal HProgress HSourceSteps HStuck HTargetSteps.
      fix IH 7. intros j b t i a s Hsim.
      destruct Hsim as
        [ j b t i a s Hfin
        | j b t i a s Hstuck
        | j b t i a s s' a' Hstep HR Hsim
        | j b t i a s Hprogress Ht
        | j j' b t i i' a s Ht Hs Hgfp ].
      - apply HFinal. assumption.
      - apply HStuck. assumption.
      - eapply HSourceSteps; now eauto.
      - apply HTargetSteps.
        { assumption. }
        intros t' Hstep.
        destruct (Ht _ Hstep) as (j' & b' & HR & Hsim).
        do 2 eexists. now eauto.
      - eapply HProgress; now eauto.
    Qed.
  End GSimInd.

  Register Scheme gsim_ind as ind_nodep for gsim.

  Lemma gsim_weaken_t: ∀ j b t i a s,
    gsim j b t i a s ->
    ∀ w, b ⊑ w ->
    gsim j w t i a s.
  Proof using Type.
    intros j b t i a s Hsim w Hle.
    induction Hsim as
      [ j b t i a s Hfin
      | j b t i a s Hstuck
      | j b t i i' a s s' a' Hstep HR Hsim IHs
      | j b t i a s Hprogress IHt
      | j j' b t i i' a s Ht Hs Hgfp]
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
      destruct (IHt _ Hstep) as (j' & b' & Hlt' & Hsim & IH).
      destruct Hle as [ Hlt | -> ].
      + do 2 eexists. split.
        * eassumption.
        * apply IH. now left.
      + do 2 eexists. split; eauto.
    - eapply GProgress; try eassumption.
  Qed.

  Lemma gsim_weaken_s: ∀ j b t i a s,
    gsim j b t i a s ->
    ∀ w, a ⊑ w ->
    gsim j b t i w s.
  Proof using Type.
    intros j b t i a s Hsim w Hle.
    induction Hsim as
      [ j b t i a s Hfin
      | j b t i a s Hstuck
      | j b t i i' a s s' a' Hstep HR Hsim IHs
      | j b t i a s Hprogress IHt
      | j j' b t i i' a s Ht Hs Hgfp]
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
      destruct (IHt _ Hstep) as (j' & b' & Hlt' & Hsim & IH).
      do 2 eexists. split.
      + eassumption.
      + apply IH. assumption.
    - eapply GProgress; try eassumption.
  Qed.
End GSimDef.
