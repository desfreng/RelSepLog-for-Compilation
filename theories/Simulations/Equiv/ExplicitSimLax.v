From RSL Require Import Prelude.

From RSL.Commons Require Export Language WfRel.

From Coinduction Require Import all.

Section ESimLaxDef.
  Context {Λₜ Λₛ: lang}.
  Context (W: WfRel) (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).
  Context (Φ: value Λₜ * memory -> value Λₛ * memory -> Prop).

  Inductive esim_lax_lfp' (gfp: W -> state Λₜ -> state Λₛ -> Prop)
    : W -> state Λₜ -> state Λₛ -> Prop :=
  | ELaxRelated : ∀ i t s,
    both_final Φ t s ->
    esim_lax_lfp' gfp i t s

  | ELaxSourceStuck : ∀ i t s,
    stuck Pₛ s ->
    esim_lax_lfp' gfp i t s

  | ELaxSourceSteps : ∀ i i' t s s',
    Pₛ ⊨ s ->>+ s' ->
    i' ⊏ i ->
    gfp i' t s' ->
    esim_lax_lfp' gfp i t s

  | ELaxTargetSteps : ∀ i t s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ i', i' ⊏ i ∧ gfp i' t' s) ->
    esim_lax_lfp' gfp i t s

  | ELaxBothSteps : ∀ i t s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ i' s', Pₛ ⊨ s ->>+ s' ∧ gfp i' t' s') ->
    esim_lax_lfp' gfp i t s.

  Program Definition esim_lax_lfp : mon (W -> state Λₜ -> state Λₛ -> Prop) :=
    {| body := esim_lax_lfp' |}.
  Next Obligation.
    intros gfp gfp' Hgfp i t s Hsim.
    inv Hsim as [ | | | ? ? ? Hprogress Ht |  ? ? ? Hprogress Hboth].
    - eapply ELaxRelated; eassumption.
    - eapply ELaxSourceStuck; eassumption.
    - eapply ELaxSourceSteps; eauto.
      now apply Hgfp.
    - eapply ELaxTargetSteps; eauto.
      intros t' Hstep.
      destruct (Ht _ Hstep) as (i' & ? & ?).
      exists i'. split; auto.
      now apply Hgfp.
    - eapply ELaxBothSteps; eauto.
      intros t' Hstep.
      destruct (Hboth _ Hstep) as (i' & s' & ? & ?).
      exists i', s'. split; auto.
      now apply Hgfp.
  Qed.

  Lemma esim_lax_unroll i t s :
    gfp esim_lax_lfp i t s -> esim_lax_lfp' (gfp esim_lax_lfp) i t s.
  Proof using Type. apply (gfp_fp esim_lax_lfp). Qed.

  Lemma esim_lax_roll i t s :
    esim_lax_lfp' (gfp esim_lax_lfp) i t s -> gfp esim_lax_lfp i t s.
  Proof using Type. apply (gfp_fp esim_lax_lfp). Qed.

  Definition esim_lax  := gfp esim_lax_lfp.
End ESimLaxDef.
