From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.Commons.

(* Set Mangle Names. *)

Section ISimDef.
  Context {Λₜ Λₛ: lang}.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Inductive isim_lfp'
    (gfp: state Λₜ -> state Λₛ -> Prop) : state Λₜ -> state Λₛ-> Prop :=
  | IBothFinal : ∀ t s,
    is_final Φ t s -> isim_lfp' gfp t s

  | ISourceStuck : ∀ t s,
    stuck Pₛ s -> isim_lfp' gfp t s

  | ISourceSteps : ∀ t s s',
    Pₛ ⊨ s ->> s' -> isim_lfp' gfp t s' -> isim_lfp' gfp t s

  | ITargetSteps : ∀ t s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> isim_lfp' gfp t' s) ->
    isim_lfp' gfp t s

  | IBothSteps : ∀ t s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ s', Pₛ ⊨ s ->> s' ∧ gfp t' s') ->
    isim_lfp' gfp t s.

  Instance isim_lfp'_proper : Proper (leq ==> leq) isim_lfp'.
  Proof.
    intros gfp gfp' Hgfp s t H. induction H as [ | | | | ? ? ? H ];
      try (econstructor; eassumption || now apply Hlfp).
    apply IBothSteps; eauto. intros t' Hstep.
    destruct (H _ Hstep) as (? & ? & ?).
    eexists. split; eassumption || now apply Hgfp.
  Qed.

  Definition isim_lfp : mon (state Λₜ -> state Λₛ -> Prop) := {| body := isim_lfp' |}.

  Lemma isim_unroll t s :
    gfp isim_lfp t s -> isim_lfp' (gfp isim_lfp) t s.
  Proof. apply (gfp_fp isim_lfp). Qed.

  Lemma isim_roll t s :
    isim_lfp' (gfp isim_lfp) t s -> gfp isim_lfp t s.
  Proof. apply (gfp_fp isim_lfp). Qed.

  Definition isim := gfp isim_lfp.
End ISimDef.
