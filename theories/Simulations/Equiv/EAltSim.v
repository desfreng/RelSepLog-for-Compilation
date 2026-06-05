From RSL Require Import Prelude.

From Coinduction Require Import all.

Section EAltSimDef.
  Context {Λₜ Λₛ: lang}.
  Context (J I: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Variant ealt_sim_lfp' (gfp: J -> state Λₜ -> I -> state Λₛ -> Prop)
    : J -> state Λₜ -> I -> state Λₛ -> Prop :=
  | EAltBothFinal : ∀ j t i s,
    both_final Φ t s -> ealt_sim_lfp' gfp j t i s

  | EAltSourceStuck : ∀ j t i s,
    stuck Pₛ s -> ealt_sim_lfp' gfp j t i s

  | EAltSourceSteps : ∀ j j' t i i' s s',
    Pₛ ⊨ s ->> s' ->
    i' ⊏ i ->
    gfp  j' t i' s' ->
    ealt_sim_lfp' gfp j t i s

  | EAltTargetSteps : ∀ j t i s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' ->
           ∃ j' i',
             j' ⊏ j ∧
             gfp j' t' i' s) ->
    ealt_sim_lfp' gfp j t i s

  | EAltBothSteps : ∀ j t i s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' ->
           ∃ j' i' s' ,
             Pₛ ⊨ s ->> s' ∧
             gfp j' t' i' s') ->
    ealt_sim_lfp' gfp j t i s.

  Instance ealt_sim_mono : Proper (leq ==> leq) ealt_sim_lfp'.
  Proof using Type.
    intros gfp gfp' Hgfp  j t  i s Hsim.
    induction Hsim as
      [ j t i s Hfin
      | j t i s Hstuck
      | j j' t i i' s Hstep Hlt Hs
      | j t i s Hprogress Ht
      | j t i s Hprogress Hboth ].
    - econstructor; eassumption.
    - econstructor; eassumption.
    - eapply EAltSourceSteps; eauto.
      apply Hgfp. eassumption.
    - apply EAltTargetSteps; auto. intros ? Hstep.
      edestruct (Ht _ Hstep) as (j' & i' & HR & Isim).
      do 2 eexists. split; eauto.
      apply Hgfp. eassumption.
    - apply EAltBothSteps; auto. intros ? Hstep.
      edestruct (Hboth _ Hstep) as (j' & i' & s' & HR & Isim).
      do 3 eexists. split; eauto.
      apply Hgfp. eassumption.
  Qed.

  Definition ealt_sim_lfp : mon (J -> state Λₜ -> I -> state Λₛ -> Prop) :=
    {| body := ealt_sim_lfp' |}.

  Lemma ealt_sim_unroll j t i s :
    gfp ealt_sim_lfp j t i s -> ealt_sim_lfp' (gfp ealt_sim_lfp) j t i s.
  Proof using Type. apply (gfp_fp ealt_sim_lfp). Qed.

  Lemma ealt_sim_roll j t i s :
    ealt_sim_lfp' (gfp ealt_sim_lfp) j t i s -> gfp ealt_sim_lfp j t i s.
  Proof using Type. apply (gfp_fp ealt_sim_lfp). Qed.

  Definition ealt_sim := gfp ealt_sim_lfp.

  Lemma ealt_sim_idx_mono (R: Chain ealt_sim_lfp):
    ∀ j t i s,
    (elem R) j t i s ->
    ∀ j' i',
    j ⊑ j' ->
    i ⊑ i' ->
    (elem R) j' t i' s.
  Proof using Type.
    apply tower.
    { intros P Hp j t i s Hinf j' i' Ht Hs.
      intros Q Hq. eapply (Hp _ Hq); try eassumption.
      now apply Hinf.
    }
    clear R. intros R CIH j t i s Hsim.
    induction Hsim as
      [ j t i s Hfin
      | j t i s Hstuck
      | j j'' t i i'' s Hstep Hlt Hs
      | j t i s Hprogress Ht
      | j t i s Hprogress Hboth ]; intros j' i' Hleₜ Hleₛ.
    - now constructor.
    - now constructor.
    - destruct Hleₛ as [ Hltₛ | -> ].
      + eapply EAltSourceSteps; try eassumption.
        eapply CIH.
        * eassumption.
        * reflexivity.
        * now left.
      + eapply EAltSourceSteps; eassumption.
    - destruct Hleₜ as [ Hltₜ | -> ].
      + apply EAltTargetSteps.
        { eassumption. }
        intros t' Hstep.
        destruct (Ht _ Hstep) as (j'' & i'' & Hlt & Hsim).
        exists j, i''; split. 1: assumption.
        eapply CIH.
        * eassumption.
        * now left.
        * reflexivity.
      + apply EAltTargetSteps; eassumption.
    - apply EAltBothSteps.
      { assumption. }
      intros t' Hstep.
      destruct (Hboth _ Hstep) as (j'' & i'' & s' & Hsteps & Hsim).
      exists j'', i'', s'. split; now auto.
  Qed.
End EAltSimDef.
