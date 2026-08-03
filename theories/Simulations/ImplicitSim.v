From RSL Require Import Prelude.

From RSL.Commons Require Export Language WfRel.

From Coinduction Require Import all.

Section ISimDef.
  Context {Λt Λs: lang}.
  Context (Pt: prog Λt) (Ps: prog Λs).
  Context (Φ: value Λt * memory -> value Λs * memory -> Prop).

  Inductive isim_lfp'
    (gfp: state Λt -> state Λs -> Prop) : state Λt -> state Λs-> Prop :=
  | IRelated : ∀ t s,
    both_final Φ t s -> isim_lfp' gfp t s

  | ISourceStuck : ∀ t s,
    stuck Ps s -> isim_lfp' gfp t s

  | ISourceSteps : ∀ t s s',
    Ps ⊨ s ->> s' -> isim_lfp' gfp t s' -> isim_lfp' gfp t s

  | ITargetSteps : ∀ t s,
    can_progress Pt t ->
    (∀ t', Pt ⊨ t ->> t' -> isim_lfp' gfp t' s) ->
    isim_lfp' gfp t s

  | IBothSteps : ∀ t s,
    can_progress Pt t ->
    (∀ t', Pt ⊨ t ->> t' -> ∃ s', Ps ⊨ s ->> s' ∧ gfp t' s') ->
    isim_lfp' gfp t s.

  Instance isim_lfp'_proper : Proper (leq ==> leq) isim_lfp'.
  Proof using Type.
    intros gfp gfp' Hgfp s t H. induction H as [ | | | | ? ? ? H ];
      try (econstructor; eassumption || now apply Hlfp).
    apply IBothSteps; eauto. intros t' Hstep.
    destruct (H _ Hstep) as (? & ? & ?).
    eexists. split; eassumption || now apply Hgfp.
  Qed.

  Definition isim_lfp : mon (state Λt -> state Λs -> Prop) := {| body := isim_lfp' |}.

  Lemma isim_unroll t s :
    gfp isim_lfp t s -> isim_lfp' (gfp isim_lfp) t s.
  Proof using Type. apply (gfp_fp isim_lfp). Qed.

  Lemma isim_roll t s :
    isim_lfp' (gfp isim_lfp) t s -> gfp isim_lfp t s.
  Proof using Type. apply (gfp_fp isim_lfp). Qed.

  Definition isim := gfp isim_lfp.
End ISimDef.
