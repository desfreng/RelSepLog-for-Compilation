From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.Commons.

Section EAltSimDef.
  Context {Λₜ Λₛ: lang}.
  Context (Wₜ Wₛ: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Variant ealt_sim_lfp' (gfp: Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop)
    : Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop :=
  | EAltBothFinal : ∀ wₜ t wₛ s,
    is_final Φ t s -> ealt_sim_lfp' gfp wₜ t wₛ s

  | EAltSourceStuck : ∀ wₜ t wₛ s,
    stuck Pₛ s -> ealt_sim_lfp' gfp wₜ t wₛ s

  | EAltSourceSteps : ∀ wₜ wₜ' t wₛ wₛ' s s',
    Pₛ ⊨ s ->> s' ->
    wₛ' ⊏ wₛ ->
    gfp  wₜ' t wₛ' s' ->
    ealt_sim_lfp' gfp wₜ t wₛ s

  | EAltTargetSteps : ∀ wₜ t wₛ s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' ->
           ∃ wₜ' wₛ',
             wₜ' ⊏ wₜ ∧
             gfp wₜ' t' wₛ' s) ->
    ealt_sim_lfp' gfp wₜ t wₛ s

  | EAltBothSteps : ∀ wₜ t wₛ s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' ->
           ∃ wₜ' wₛ' s' ,
             Pₛ ⊨ s ->> s' ∧
             gfp wₜ' t' wₛ' s') ->
    ealt_sim_lfp' gfp wₜ t wₛ s.

  Instance ealt_sim_mono : Proper (leq ==> leq) ealt_sim_lfp'.
    intros gfp gfp' Hgfp  wₜ t  wₛ s Hsim.
    inv Hsim.
    - econstructor; eassumption.
    - econstructor; eassumption.
    - eapply EAltSourceSteps; eauto.
      apply Hgfp. eassumption.
    - apply EAltTargetSteps; auto. intros ? Hstep.
      edestruct (H0 _ Hstep) as (wₜ' & wₛ' & HR & Isim).
      do 2 eexists. split; eauto.
      apply Hgfp. eassumption.
    - apply EAltBothSteps; auto. intros ? Hstep.
      edestruct (H0 _ Hstep) as (wₜ' & wₛ' & s' & HR & Isim).
      do 3 eexists. split; eauto.
      apply Hgfp. eassumption.
  Qed.

  Definition ealt_sim_lfp : mon (Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop) :=
    {| body := ealt_sim_lfp' |}.

  Lemma ealt_sim_unroll wₜ t wₛ s :
    gfp ealt_sim_lfp wₜ t wₛ s -> ealt_sim_lfp' (gfp ealt_sim_lfp) wₜ t wₛ s.
  Proof using. apply (gfp_fp ealt_sim_lfp). Qed.

  Lemma ealt_sim_roll wₜ t wₛ s :
    ealt_sim_lfp' (gfp ealt_sim_lfp) wₜ t wₛ s -> gfp ealt_sim_lfp wₜ t wₛ s.
  Proof using. apply (gfp_fp ealt_sim_lfp). Qed.

  Definition ealt_sim : Wₜ -> state Λₜ -> Wₛ -> state Λₛ -> Prop
    := gfp ealt_sim_lfp.

  Lemma test (R: Chain ealt_sim_lfp):
    ∀ iₜ t iₛ s,
    (elem R) iₜ t iₛ s ->
    ∀ iₜ' iₛ',
    iₜ ⊑ iₜ' ->
    iₛ ⊑ iₛ' ->
    (elem R) iₜ' t iₛ' s.
  Proof.
    apply tower.
    - unfold inf_closed.
      intros P Hp.
      intros iₜ t iₛ s Hinf iₜ' iₛ' Ht Hs.
      intros Q Hq.
      eapply (Hp _ Hq).
      + now apply Hinf.
      + assumption.
      + assumption.
    - clear R. intros R CIH iₜ t iₛ s H.
      induction H; intros iₜ' iₛ' Ht Hs.
      + now constructor.
      + now constructor.
      + inv Hs as [ ? Hs' | ].
        * eapply EAltSourceSteps.
          { eassumption. }
          { eassumption. }
          eapply CIH.
          eassumption.
          reflexivity.
          now left.
        * eapply EAltSourceSteps.
          { eassumption. }
          { eassumption. }
          eapply CIH.
          eassumption.
          reflexivity.
          reflexivity.
      + inv Ht as [ ? Ht' | ].
        * apply EAltTargetSteps.
          { eassumption. }
          intros t' Hstep.
          destruct (H0 _ Hstep) as (? & ? & ? & ?).
          do 2 eexists.
          split.
          eassumption.
          eapply CIH.
          eassumption.
          now left.
          reflexivity.
        * apply EAltTargetSteps.
          { eassumption. }
          intros t' Hstep.
          destruct (H0 _ Hstep) as (? & ? & ? & ?).
          do 2 eexists.
          split.
          eassumption.
          eapply CIH.
          eassumption.
          reflexivity.
          reflexivity.
      + apply EAltBothSteps.
        { assumption. }
        intros t' Hstep.
        edestruct H0 as (? & ? & ? & ? & ?). eassumption.
        do 3 eexists. split.
        eassumption.
        eassumption.
  Qed.
End EAltSimDef.
