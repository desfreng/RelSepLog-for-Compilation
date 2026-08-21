From RSL Require Import Prelude.

From RSL.Commons Require Export Language Behaviors.

From Coinduction Require Import all.

Section USimDef.
  Context {Λt Λs: lang}.
  Context (Pt: prog Λt) (Ps: prog Λs).
  Context (Φ: value Λt -> value Λs -> memory -> memory -> Prop).

  Variant usim_lfp' (gfp: config Λt -> config Λs -> Prop)
    : config Λt -> config Λs -> Prop :=
  | URelated : ∀ t s,
    both_final Φ t s -> usim_lfp' gfp t s

  | UTargetSteps : ∀ t s,
    can_progress Pt t ->
    (∀ t', Pt ⊨ t ->> t' -> gfp t' s) ->
    usim_lfp' gfp t s

  | USourceSteps : ∀ t s s',
    Ps ⊨ s ->> s' ->
    gfp t s' ->
    usim_lfp' gfp t s.

  Program Definition usim_lfp : mon (config Λt -> config Λs -> Prop) :=
    {| body := usim_lfp' |}.
  Next Obligation.
    intros gfp gfp' Hgfp t s Hsim.
    induction Hsim as [ | ? ? Hprog Ht | ? ? ? Hstep Hs ].
    - now constructor.
    - eapply UTargetSteps; eauto.
      intros t' Hstep.
      by apply Hgfp, Ht.
    - eapply USourceSteps; eauto.
      by apply Hgfp, Hs.
  Qed.

  Lemma usim_unroll t s :
    gfp usim_lfp t s -> usim_lfp' (gfp usim_lfp) t s.
  Proof using Type. apply (gfp_fp usim_lfp). Qed.

  Lemma usim_roll t s :
    usim_lfp' (gfp usim_lfp) t s -> gfp usim_lfp t s.
  Proof using Type. apply (gfp_fp usim_lfp). Qed.

  Definition usim := gfp usim_lfp.

  Lemma loop_target t :
    strong_diverge Pt t ->
    ∀ s, usim t s.
  Proof using Type.
    unfold usim.
    revert t.
    coinduction C CIH.
    intros t Hdiv s.
    apply UTargetSteps.
    - by apply Hdiv.
    - intros u Hstep.
      apply CIH.
      intros t' Hrtc.
      apply Hdiv. by econstructor.
  Qed.

  Lemma loop_source s :
    diverges Ps s ->
    ∀ t, usim t s.
  Proof using Type.
    unfold usim.
    revert s.
    coinduction C CIH.
    intros s (s' & Hstep & Hdiv)%diverges_unroll t.
    eapply USourceSteps; first done.
    by apply CIH.
  Qed.
End USimDef.
