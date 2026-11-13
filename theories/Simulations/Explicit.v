From RSL Require Import Prelude.

From RSL.Language Require Export Language.
From RSL.Commons Require Export WfRel.

From Coinduction Require Import all.

Section ESimDef.
  Context {Λt Λs: lang}.
  Context (W: WfRel) (Et: genv Λt) (Es: genv Λs) (ϕ: post Λt Λs).

  Variant esim_lfp' (gfp: W -> config Λt -> config Λs -> Prop)
    : W -> config Λt -> config Λs -> Prop :=
    | ERelated : ∀ i t s,
      both_final ϕ t s ->
      esim_lfp' gfp i t s

    | ESourceStuck : ∀ i t s,
      super_stuck Es s ->
      esim_lfp' gfp i t s

    | ESourceSteps : ∀ i i' t s s',
      Es ⊨ s ->> s' ->
      i' ⊏ i ->
      gfp i' t s' ->
      esim_lfp' gfp i t s

    | ETargetSteps : ∀ i t s,
      can_progress Et t ->
      (∀ t', Et ⊨ t ->> t' -> ∃ i', i' ⊏ i ∧ gfp i' t' s) ->
      esim_lfp' gfp i t s

    | EBothSteps : ∀ i t s,
      can_progress Et t ->
      (∀ t', Et ⊨ t ->> t' -> ∃ i' s', Es ⊨ s ->> s' ∧ gfp i' t' s') ->
      esim_lfp' gfp i t s.

  Program Definition esim_lfp : mon (element W -> config Λt -> config Λs -> Prop) :=
    {| body := esim_lfp' |}.
  Next Obligation.
    intros gfp gfp' Hgfp i t s Hsim.
    inv Hsim as [ | | | ? ? ? Hprogress Ht |  ? ? ? Hprogress Hboth].
    - now constructor.
    - now constructor.
    - eapply ESourceSteps; eauto.
      now apply Hgfp.
    - eapply ETargetSteps; eauto.
      intros t' Hstep.
      destruct (Ht _ Hstep) as (i' & ? & ?).
      exists i'. split; auto.
      now apply Hgfp.
    - eapply EBothSteps; eauto.
      intros t' Hstep.
      destruct (Hboth _ Hstep) as (i' & s' & ? & ?).
      exists i', s'. split; auto.
      now apply Hgfp.
  Qed.

  Lemma esim_unroll i t s :
    gfp esim_lfp i t s -> esim_lfp' (gfp esim_lfp) i t s.
  Proof using Type. apply (gfp_fp esim_lfp). Qed.

  Lemma esim_roll i t s :
    esim_lfp' (gfp esim_lfp) i t s -> gfp esim_lfp i t s.
  Proof using Type. apply (gfp_fp esim_lfp). Qed.

  Definition esim  := gfp esim_lfp.

  Lemma esim_idx_mono (R: Chain esim_lfp):
    ∀ i t s,
    (elem R) i t s ->
    ∀ i',
    i ⊑ i' ->
    (elem R) i' t s.
  Proof using Type.
    apply tower.
    { intros P Hp i t s Hinf i' Hi.
      intros Q Hq. eapply (Hp _ Hq); try eassumption.
      now apply Hinf.
    }
    clear R. intros R CIH i t s Hsim.
    induction Hsim as
      [ i t s Hfin
      | i t s Hstuck
      | i i' t s s' Hstep Hlt Hgfp
      | i t s Hprogress IHt
      | i t s Hprogress IHboth ]; intros i'' Hle.
    - now constructor.
    - now constructor.
    - eapply ESourceSteps.
      + done.
      + by eapply lt_from_lt_le.
      + done.
    - eapply ETargetSteps.
      + done.
      + intros t' Ht.
        specialize (IHt _ Ht) as (i' & Hlt & Hgfp).
        exists i'. split.
        * by eapply lt_from_lt_le.
        * done.
    - eapply EBothSteps.
      + done.
      + intros t' Ht.
        specialize (IHboth _ Ht) as (i' & s' & Hstep & Hgfp).
        by exists i', s'.
  Qed.
End ESimDef.
