From RSL Require Import Prelude.

From RSL.Commons Require Export Language WfRel.

From Coinduction Require Import all.

Section FSimDef.
  Context {Λₜ Λₛ: lang}.
  Context (J I: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation post := (value Λₜ * memory -> value Λₛ * memory -> Prop).

  Unset Elimination Schemes.

  Inductive fsim_lfp'
    (gfp: post -> state Λₜ -> J -> I -> state Λₛ -> Prop)
    (ϕ : post) : state Λₜ -> J -> I -> state Λₛ -> Prop :=
  | FRelated : ∀ t j i s,
    both_final ϕ t s -> fsim_lfp' gfp ϕ t j i s

  | FSourceStuck : ∀ t j i s,
    stuck Pₛ s -> fsim_lfp' gfp ϕ t j i s

  | FSourceSteps : ∀ t j i i' s s',
    Pₛ ⊨ s ->> s' ->
    fsim_lfp' gfp ϕ t j i' s' ->
    fsim_lfp' gfp ϕ t j i s

  | FTargetSteps : ∀ t j i s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ j', fsim_lfp' gfp ϕ t' j' i s) ->
    fsim_lfp' gfp ϕ t j i s

  | FProgress : ∀ t j j' i i' s,
    j' ⊏ j ->
    i' ⊏ i ->
    gfp ϕ t j' i' s ->
    fsim_lfp' gfp ϕ t j i s.

  Set Elimination Schemes.

  Section FSimInd.
    Variable gfp : post -> state Λₜ -> J -> I -> state Λₛ -> Prop.
    Variable ϕ : post.
    Variable P : state Λₜ -> J -> I -> state Λₛ -> Prop.

    Hypothesis HFinal:
      ∀ t j i s, both_final ϕ t s -> P t j i s.

    Hypothesis HStuck:
      ∀ t j i s, stuck Pₛ s -> P t j i s.

    Hypothesis HSourceSteps:
      ∀ t j i i' s s',
      Pₛ ⊨ s ->> s' ->
      fsim_lfp' gfp ϕ t j i' s' ->
      P t j i' s' ->
      P t j i s.

    Hypothesis HTargetSteps:
      ∀ t j i s,
      can_progress Pₜ t ->
      (∀ t', Pₜ ⊨ t ->> t' ->
             ∃ j',
               fsim_lfp' gfp ϕ t' j' i s ∧
               P t' j' i s) ->
      P t j i s.

    Hypothesis HProgress:
      ∀ t j j' i i' s,
      j' ⊏ j ->
      i' ⊏ i ->
      gfp ϕ t j' i' s ->
      P t j i s.

    Lemma fsim_lfp'_ind: ∀ t j i s,
      fsim_lfp' gfp ϕ t j i s -> P t j i s.
    Proof using HFinal HProgress HSourceSteps HStuck HTargetSteps.
      fix IH 5. intros t j i s Hsim.
      destruct Hsim as
        [ t j i s Hfin
        | t j i s Hstuck
        | t j i' i s s' Hstep Hsim
        | t j i s Hprogress Ht
        | t j j' i i' s Ht Hs Hgfp ].
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
    intros gfp gfp' Hgfp ϕ t j i s Hsim.
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

  Definition fsim := (gfp fsim_lfp).

  Lemma fsim_unroll ϕ t j i s :
    gfp fsim_lfp ϕ t j i s -> fsim_lfp' (gfp fsim_lfp) ϕ t j i s.
  Proof using Type. apply (gfp_fp fsim_lfp). Qed.

  Lemma fsim_roll ϕ t j i s :
    fsim_lfp' (gfp fsim_lfp) ϕ t j i s -> gfp fsim_lfp ϕ t j i s.
  Proof using Type. apply (gfp_fp fsim_lfp). Qed.

  Lemma idx_mono (R: Chain fsim_lfp) ϕ t j i s:
    ∀ ϕ' j' i',
    (∀ vt vs, ϕ vt vs -> ϕ' vt vs) ->
    j ⊑ j' ->
    i ⊑ i' ->
    (elem R) ϕ t j i s ->
    (elem R) ϕ' t j' i' s.
  Proof using Type.
    revert ϕ t j i s.
    apply tower.
    - intros P Hp.
      intros ϕ t j i s ϕ' j' i' Hϕ Hj Hi Hinf.
      intros Q Hq.
      eapply (Hp _ Hq).
      4: now apply Hinf. all: easy.
    - intros C CIH ϕ t j i s ϕ' j' i' Hϕ Hj Hi Hsim.
      revert ϕ' j' i' Hϕ Hj Hi.
      induction Hsim as [ ? t ? s Hfin
                        | ? t ? s Hstuck
                        | ? t ? ? s s' Hstep Hsim IH
                        | ? t ? s Hprog IH
                        | ? ? t  ? ? s Htt Hss Hsim ];
        intros ? ? ? Hϕ Hj Hi.
      + constructor.
        destruct Hfin as (vt & vs & Hfint & Hfins & Hfin).
        exists vt, vs; now auto.
      + now constructor.
      + eapply FSourceSteps.
        { eassumption. }
        apply IH; now auto.
      + apply FTargetSteps.
        { assumption. }
        intros t' Hstep.
        destruct (IH _ Hstep) as (? & Hsim & IHt).
        eexists. apply IHt; assumption || reflexivity.
      + destruct Hj as [ Hj | -> ]; destruct Hi as [ Hi | -> ];
          eapply FProgress; try eassumption;
          eapply (CIH _ _ _ _ _ _ _ _ _ _ _ Hsim).
        Unshelve.
        all: easy || now left.
  Qed.

  Lemma fsim_mono ϕ t j i s:
    ∀ ϕ' j' i',
    (∀ vt vs, ϕ vt vs -> ϕ' vt vs) ->
    j ⊑ j' ->
    i ⊑ i' ->
    fsim ϕ t j i s ->
    fsim ϕ' t j' i' s.
  Proof using Type. by apply idx_mono. Qed.

  Lemma fsim_lfp_mono (R: Chain fsim_lfp) ϕ t j i s:
    ∀ ϕ' j' i',
    (∀ vt vs, ϕ vt vs -> ϕ' vt vs) ->
    j ⊑ j' ->
    i ⊑ i' ->
    fsim_lfp (elem R) ϕ t j i s ->
    fsim_lfp (elem R) ϕ' t j' i' s.
  Proof using Type. by apply idx_mono. Qed.
End FSimDef.
