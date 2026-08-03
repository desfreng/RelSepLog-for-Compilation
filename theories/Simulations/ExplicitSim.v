From RSL Require Import Prelude.

From RSL.Commons Require Export Language WfRel.

From Coinduction Require Import all.

Section ESimDef.
  Context {Λt Λs: lang}.
  Context (W: WfRel) (Pt: prog Λt) (Ps: prog Λs).
  Context (Φ: value Λt * memory -> value Λs * memory -> Prop).

  Variant esim_lfp' (gfp: W -> state Λt -> state Λs -> Prop)
    : W -> state Λt -> state Λs -> Prop :=
  | ERelated : ∀ i t s,
    both_final Φ t s -> esim_lfp' gfp i t s

  | ESourceStuck : ∀ i t s,
    stuck Ps s -> esim_lfp' gfp i t s

  | ESourceSteps : ∀ i i' t s s',
    Ps ⊨ s ->> s' ->
    i' ⊏ i ->
    gfp i' t s' ->
    esim_lfp' gfp i t s

  | ETargetSteps : ∀ i t s,
    can_progress Pt t ->
    (∀ t', Pt ⊨ t ->> t' -> ∃ i', i' ⊏ i ∧ gfp i' t' s) ->
    esim_lfp' gfp i t s

  | EBothSteps : ∀ i t s,
    can_progress Pt t ->
    (∀ t', Pt ⊨ t ->> t' -> ∃ i' s', Ps ⊨ s ->> s' ∧ gfp i' t' s') ->
    esim_lfp' gfp i t s.

  Program Definition esim_lfp : mon (element W -> state Λt -> state Λs -> Prop) :=
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
End ESimDef.
