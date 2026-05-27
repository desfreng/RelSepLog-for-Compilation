From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.Commons.

Section FSimDef.
  Context {Λₜ Λₛ: lang}.
  Context (Wₜ Wₛ: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Unset Elimination Schemes.

  Inductive fsim_lfp' (gfp: Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop)
    : Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop :=
  | FBothFinal : ∀ j t i s,
    is_final Φ t s -> fsim_lfp' gfp j t i s

  | FSourceStuck : ∀ j t i s,
    stuck Pₛ s -> fsim_lfp' gfp j t i s

  | FSourceSteps : ∀ j t i i' s s',
    Pₛ ⊨ s ->> s' ->
    fsim_lfp' gfp j t i' s' ->
    fsim_lfp' gfp j t i s

  | FTargetSteps : ∀ j t i s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ j', fsim_lfp' gfp j' t' i s) ->
    fsim_lfp' gfp j t i s

  | FProgress : ∀ j j' t i i' s,
    j' ⊏ j ->
    i' ⊏ i ->
    gfp j' t i' s ->
    fsim_lfp' gfp j t i s.

  Set Elimination Schemes.

  Section FSimInd.
    Variable gfp : Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop.
    Variable P : Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop.

    Hypothesis HFinal:
      ∀ j t i s, is_final Φ t s -> P j t i s.

    Hypothesis HStuck:
      ∀ j t i s, stuck Pₛ s -> P j t i s.

    Hypothesis HSourceSteps:
      ∀ j t i i' s s',
      Pₛ ⊨ s ->> s' ->
      fsim_lfp' gfp j t i' s' ->
      P j t i' s' ->
      P j t i s.

    Hypothesis HTargetSteps:
      ∀ j t i s,
      can_progress Pₜ t ->
      (∀ t', Pₜ ⊨ t ->> t' ->
             ∃ j',
               fsim_lfp' gfp j' t' i s ∧
               P j' t' i s) ->
      P j t i s.

    Hypothesis HProgress:
      ∀ j j' t i i' s,
      j' ⊏ j ->
      i' ⊏ i ->
      gfp j' t i' s ->
      P j t i s.

    Lemma fsim_lfp'_ind: ∀ j t i s,
      fsim_lfp' gfp j t i s -> P j t i s.
    Proof using HFinal HProgress HSourceSteps HStuck HTargetSteps.
      fix IH 5. intros j t i s Hsim.
      destruct Hsim as
        [ j t i s Hfin
        | j t i s Hstuck
        | j t i' i s s' Hstep Hsim
        | j t i s Hprogress Ht
        | j j' t i i' s Ht Hs Hgfp ].
      - apply HFinal. assumption.
      - apply HStuck. assumption.
      - eapply HSourceSteps; now eauto.
      - apply HTargetSteps.
        { assumption. }
        intros t' Hstep.
        destruct (Ht _ Hstep) as (j' & Hsim).
        exists j'. now auto.
      - eapply HProgress; now eauto.
    Qed.
  End FSimInd.

  Register Scheme fsim_lfp'_ind as ind_nodep for fsim_lfp'.

  Instance fsim_lfp'_mono : Proper (leq ==> leq) fsim_lfp'.
  Proof using Type.
    intros gfp gfp' Hgfp j t i s Hsim.
    induction Hsim as [ | | | ? ? ? ? Hprogress Ht |  ? ? ? Hprogress Hboth].
    - econstructor; eassumption.
    - econstructor; eassumption.
    - econstructor; eassumption.
    - apply FTargetSteps; auto. intros ? Hstep.
      destruct (Ht _ Hstep) as (j' & Isim & IH).
      exists j'. auto.
    - eapply FProgress; try eassumption.
      apply Hgfp. eassumption.
  Qed.

  Definition fsim_lfp : mon (Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop) :=
    {| body := fsim_lfp' |}.

  Lemma fsim_unroll j t i s :
    gfp fsim_lfp j t i s -> fsim_lfp' (gfp fsim_lfp) j t i s.
  Proof using Type. apply (gfp_fp fsim_lfp). Qed.

  Lemma fsim_roll j t i s :
    fsim_lfp' (gfp fsim_lfp) j t i s -> gfp fsim_lfp j t i s.
  Proof using Type. apply (gfp_fp fsim_lfp). Qed.

  Definition fsim  := gfp fsim_lfp.
End FSimDef.

Section GenericRules.
  Context {Λₜ Λₛ: lang}.
  Context (Wₜ Wₛ: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Lemma idx_mono (R: Chain (fsim_lfp Wₜ Wₛ Pₜ Pₛ Φ)):
    ∀ j i t s,
    (elem R) j t i s ->
    ∀ j' i',
    j ⊑ j' ->
    i ⊑ i' ->
    (elem R) j' t i' s.
  Proof using Type.
    apply tower.
    - intros P Hp.
      intros j i t s Hinf j' i' Ht Hs.
      intros Q Hq.
      eapply (Hp _ Hq).
      + now apply Hinf.
      + assumption.
      + assumption.
    - intros C CIH j t i s Hsim.
      induction Hsim as [ ? t ? s Hfin
                        | ? t ? s Hstuck
                        | ? t ? ? s s' Hstep Hsim IH
                        | ? t ? s Hprog IH
                        | ? ? t  ? ? s Htt Hss Hsim ];
        intros ? ? Ht Hs.
      + now constructor.
      + now constructor.
      + eapply FSourceSteps.
        { eassumption. }
        apply IH; assumption || reflexivity.
      + apply FTargetSteps.
        { assumption. }
        intros t' Hstep.
        destruct (IH _ Hstep) as (? & Hsim & IHt).
        eexists. apply IHt; assumption || reflexivity.
      + destruct Hs as [ Hs | -> ]; destruct Ht as [ Ht | -> ];
          eapply FProgress; try eassumption;
          eapply CIH; eassumption || now constructor.
  Qed.

  Lemma fsim_mono:
    ∀ j i t s,
    fsim Wₜ Wₛ Pₜ Pₛ Φ j t i s ->
    ∀ j' i',
    j ⊑ j' ->
    i ⊑ i' ->
    fsim Wₜ Wₛ Pₜ Pₛ Φ  j' t i' s.
  Proof using Type.
    intros j t i s Hsim.
    now apply idx_mono.
  Qed.

End GenericRules.
