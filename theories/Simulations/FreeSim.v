From RSL Require Import Prelude.

From Coinduction Require Import all.

Section FSimDef.
  Context {Λₜ Λₛ: lang}.
  Context (J I: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation post := (value Λₜ -> value Λₛ -> Prop).

  Unset Elimination Schemes.

  Inductive fsim_lfp'
    (gfp: post -> J -> state Λₜ -> I -> state Λₛ -> Prop)
    (Φ : post) : J -> state Λₜ -> I -> state Λₛ -> Prop :=
  | FRelated : ∀ j t i s,
    both_final Φ t s -> fsim_lfp' gfp Φ j t i s

  | FSourceStuck : ∀ j t i s,
    stuck Pₛ s -> fsim_lfp' gfp Φ j t i s

  | FSourceSteps : ∀ j t i i' s s',
    Pₛ ⊨ s ->> s' ->
    fsim_lfp' gfp Φ j t i' s' ->
    fsim_lfp' gfp Φ j t i s

  | FTargetSteps : ∀ j t i s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ j', fsim_lfp' gfp Φ j' t' i s) ->
    fsim_lfp' gfp Φ j t i s

  | FProgress : ∀ j j' t i i' s,
    j' ⊏ j ->
    i' ⊏ i ->
    gfp Φ j' t i' s ->
    fsim_lfp' gfp Φ j t i s.

  Set Elimination Schemes.

  Section FSimInd.
    Variable gfp : post -> J -> state Λₜ -> I -> state Λₛ -> Prop.
    Variable Φ : post.
    Variable P : J -> state Λₜ -> I -> state Λₛ -> Prop.

    Hypothesis HFinal:
      ∀ j t i s, both_final Φ t s -> P j t i s.

    Hypothesis HStuck:
      ∀ j t i s, stuck Pₛ s -> P j t i s.

    Hypothesis HSourceSteps:
      ∀ j t i i' s s',
      Pₛ ⊨ s ->> s' ->
      fsim_lfp' gfp Φ j t i' s' ->
      P j t i' s' ->
      P j t i s.

    Hypothesis HTargetSteps:
      ∀ j t i s,
      can_progress Pₜ t ->
      (∀ t', Pₜ ⊨ t ->> t' ->
             ∃ j',
               fsim_lfp' gfp Φ j' t' i s ∧
               P j' t' i s) ->
      P j t i s.

    Hypothesis HProgress:
      ∀ j j' t i i' s,
      j' ⊏ j ->
      i' ⊏ i ->
      gfp Φ j' t i' s ->
      P j t i s.

    Lemma fsim_lfp'_ind: ∀ j t i s,
      fsim_lfp' gfp Φ j t i s -> P j t i s.
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
    intros gfp gfp' Hgfp Φ j t i s Hsim.
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

  Definition fsim_lfp := {| body := fsim_lfp' |}.

  Lemma fsim_unroll Φ j t i s :
    gfp fsim_lfp Φ j t i s -> fsim_lfp' (gfp fsim_lfp) Φ j t i s.
  Proof using Type. apply (gfp_fp fsim_lfp). Qed.

  Lemma fsim_roll Φ j t i s :
    fsim_lfp' (gfp fsim_lfp) Φ j t i s -> gfp fsim_lfp Φ j t i s.
  Proof using Type. apply (gfp_fp fsim_lfp). Qed.

  Definition fsim := gfp fsim_lfp.

  Lemma idx_mono (R: Chain fsim_lfp) Φ:
    ∀ j i t s,
    (elem R) Φ j t i s ->
    ∀ j' i',
    j ⊑ j' ->
    i ⊑ i' ->
    (elem R) Φ j' t i' s.
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

  Lemma fsim_mono Φ:
    ∀ j i t s,
    fsim Φ j t i s ->
    ∀ j' i',
    j ⊑ j' ->
    i ⊑ i' ->
    fsim Φ j' t i' s.
  Proof using Type.
    intros j t i s Hsim.
    now apply idx_mono.
  Qed.

  Lemma fsim_lfp_mono (R: Chain fsim_lfp) Φ:
    ∀ j i t s,
    fsim_lfp (elem R) Φ j t i s ->
    ∀ j' i',
    j ⊑ j' ->
    i ⊑ i' ->
    fsim_lfp (elem R) Φ j' t i' s.
  Proof using Type.
    intros j t i s Hsim.
    now apply idx_mono.
  Qed.
End FSimDef.
