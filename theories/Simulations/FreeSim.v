From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.Commons.

(* Set Mangle Names. *)

Section FSimDef.
  Context {Λₜ Λₛ: lang}.
  Context (Wₜ Wₛ: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Unset Elimination Schemes.

  Inductive fsim_lfp' (gfp: Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop)
    : Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop :=
  | FBothFinal : ∀ iₜ t iₛ s,
    is_final Φ t s -> fsim_lfp' gfp iₜ t iₛ s

  | FSourceStuck : ∀ iₜ t iₛ s,
    stuck Pₛ s -> fsim_lfp' gfp iₜ t iₛ s

  | FSourceSteps : ∀ iₜ t iₛ iₛ' s s',
    Pₛ ⊨ s ->> s' ->
    fsim_lfp' gfp iₜ t iₛ' s' ->
    fsim_lfp' gfp iₜ t iₛ s

  | FTargetSteps : ∀ iₜ t iₛ s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ iₜ', fsim_lfp' gfp iₜ' t' iₛ s) ->
    fsim_lfp' gfp iₜ t iₛ s

  | FProgress : ∀ iₜ iₜ' t iₛ iₛ' s,
    iₜ' ⊏ iₜ ->
    iₛ' ⊏ iₛ ->
    gfp iₜ' t iₛ' s ->
    fsim_lfp' gfp iₜ t iₛ s.

  Set Elimination Schemes.

  Section FSimInd.
    Variable gfp : Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop.
    Variable P : Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop.

    Hypothesis HFinal:
      ∀ iₜ t iₛ s, is_final Φ t s -> P iₜ t iₛ s.

    Hypothesis HStuck:
      ∀ iₜ t iₛ s, stuck Pₛ s -> P iₜ t iₛ s.

    Hypothesis HSourceSteps:
      ∀ iₜ t iₛ iₛ' s s',
      Pₛ ⊨ s ->> s' ->
      fsim_lfp' gfp iₜ t iₛ' s' ->
      P iₜ t iₛ' s' ->
      P iₜ t iₛ s.

    Hypothesis HTargetSteps:
      ∀ iₜ t iₛ s,
      can_progress Pₜ t ->
      (∀ t', Pₜ ⊨ t ->> t' ->
             ∃ iₜ',
               fsim_lfp' gfp iₜ' t' iₛ s ∧
               P iₜ' t' iₛ s) ->
      P iₜ t iₛ s.

    Hypothesis HProgress:
      ∀ iₜ iₜ' t iₛ iₛ' s,
      iₜ' ⊏ iₜ ->
      iₛ' ⊏ iₛ ->
      gfp iₜ' t iₛ' s ->
      P iₜ t iₛ s.

    Lemma fsim_lfp'_ind: ∀ iₜ t iₛ s,
      fsim_lfp' gfp iₜ t iₛ s -> P iₜ t iₛ s.
    Proof.
      fix IH 5. intros iₜ t iₛ s Hsim.
      destruct Hsim as
        [ iₜ t iₛ s Hfin
        | iₜ t iₛ s Hstuck
        | iₜ t iₛ' iₛ s s' Hstep Hsim
        | iₜ t iₛ s Hprogress Ht
        | iₜ iₜ' t iₛ iₛ' s Ht Hs Hgfp ].
      - apply HFinal. assumption.
      - apply HStuck. assumption.
      - eapply HSourceSteps; now eauto.
      - apply HTargetSteps.
        { assumption. }
        intros t' Hstep.
        destruct (Ht _ Hstep) as (iₜ' & Hsim).
        exists iₜ'. now auto.
      - eapply HProgress; now eauto.
    Qed.
  End FSimInd.

  Register Scheme fsim_lfp'_ind as ind_nodep for fsim_lfp'.

  Instance fsim_lfp'_mono : Proper (leq ==> leq) fsim_lfp'.
  Proof.
    intros gfp gfp' Hgfp iₜ t iₛ s Hsim.
    induction Hsim as [ | | | ? ? ? ? Hprogress Ht |  ? ? ? Hprogress Hboth].
    - econstructor; eassumption.
    - econstructor; eassumption.
    - econstructor; eassumption.
    - apply FTargetSteps; auto. intros ? Hstep.
      destruct (Ht _ Hstep) as (i & Isim & IH).
      exists i. auto.
    - eapply FProgress; try eassumption.
      apply Hgfp. eassumption.
  Qed.

  Definition fsim_lfp : mon (Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop) :=
    {| body := fsim_lfp' |}.

  Lemma fsim_unroll iₜ t iₛ s :
    gfp fsim_lfp iₜ t iₛ s -> fsim_lfp' (gfp fsim_lfp) iₜ t iₛ s.
  Proof. apply (gfp_fp fsim_lfp). Qed.

  Lemma fsim_roll iₜ t iₛ s :
    fsim_lfp' (gfp fsim_lfp) iₜ t iₛ s -> gfp fsim_lfp iₜ t iₛ s.
  Proof. apply (gfp_fp fsim_lfp). Qed.

  Definition fsim  := gfp fsim_lfp.

  Lemma idx_mono (R: Chain fsim_lfp):
    ∀ iₜ iₛ t s,
    (elem R) iₜ t iₛ s ->
    ∀ iₜ' iₛ',
    iₜ ⊑ iₜ' ->
    iₛ ⊑ iₛ' ->
    (elem R) iₜ' t iₛ' s.
  Proof.
    apply tower.
    - intros P Hp.
      intros iₜ iₛ t s Hinf iₜ' iₛ' Ht Hs.
      intros Q Hq.
      eapply (Hp _ Hq).
      + now apply Hinf.
      + assumption.
      + assumption.
    - intros C CIH iₜ t iₛ s Hsim.
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
      + inv Hs as [ ? Hs' | ]; inv Ht as [ ? Ht' | ];
          eapply FProgress; try eassumption;
          eapply CIH; eassumption || now constructor.
  Qed.

  Lemma fsim_mono :
    ∀ iₜ iₛ t s,
    fsim iₜ t iₛ s ->
    ∀ iₜ' iₛ',
    iₜ ⊑ iₜ' ->
    iₛ ⊑ iₛ' ->
    fsim iₜ' t iₛ' s.
  Proof.
    intros iₜ t iₛ s Hsim.
    now apply idx_mono.
  Qed.

  Lemma fsim_wf_ind : ∀ t s,
    (∀ iₜ iₛ,
       (∀ iₜ' iₛ', iₜ' ⊏ iₜ -> iₛ' ⊏ iₛ -> fsim iₜ' t iₛ' s) ->
       fsim iₜ t iₛ s) ->
    ∀ iₜ iₛ, fsim iₜ t iₛ s.
  Proof.
    intros t s Hstep iₜ.
    induction iₜ as [iₜ IH] using (well_founded_induction wf).
    intros iₛ.
    apply Hstep.
    intros iₜ' iₛ' Ht' Hs'.
    apply IH.
    - exact Ht'.
  Qed.
End FSimDef.
