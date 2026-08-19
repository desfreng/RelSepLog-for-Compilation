From RSL Require Import Prelude.

From RSL.Commons Require Export Language.

From Coinduction Require Import all.

Section LSimDef.
  Context {Λt Λs: lang}.
  Context (Pt: prog Λt) (Ps: prog Λs).
  Context (Φ: value Λt -> value Λs -> memory -> memory -> Prop).

  Variant lsim_lfp' (gfp: state Λt -> state Λs -> Prop)
    : state Λt -> state Λs -> Prop :=
  | LRelated : ∀ t s,
    both_final Φ t s -> lsim_lfp' gfp t s

  | LBothSteps : ∀ t s,
    can_progress Pt t ->
    (∀ t', Pt ⊨ t ->> t' -> ∃ s', Ps ⊨ s ->> s' ∧ gfp t' s') ->
    lsim_lfp' gfp t s.

  Program Definition lsim_lfp : mon (state Λt -> state Λs -> Prop) :=
    {| body := lsim_lfp' |}.
  Next Obligation.
    intros gfp gfp' Hgfp t s Hsim.
    induction Hsim as [ | ? ? Hprog Hboth].
    - now constructor.
    - eapply LBothSteps; eauto.
      intros t' Hstep.
      destruct (Hboth _ Hstep) as (s' & ? & ?).
      exists s'. split; auto.
      now apply Hgfp.
  Qed.

  Lemma lsim_unroll t s :
    gfp lsim_lfp t s -> lsim_lfp' (gfp lsim_lfp) t s.
  Proof using Type. apply (gfp_fp lsim_lfp). Qed.

  Lemma lsim_roll t s :
    lsim_lfp' (gfp lsim_lfp) t s -> gfp lsim_lfp t s.
  Proof using Type. apply (gfp_fp lsim_lfp). Qed.

  Definition lsim  := gfp lsim_lfp.
End LSimDef.
