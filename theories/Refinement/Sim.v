From stdpp Require Import prelude.
From stdpp Require Import tactics.

From Coinduction Require Import all.

From RSL.Commons Require Import Language.

(* Set Mangle Names. *)

Section SimDef.
  Context {Λₜ Λₛ: lang}.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Definition is_final (t: state Λₜ) (s: state Λₛ) : Prop :=
    ∃ vₜ vₛ, is_final t = Some vₜ ∧ is_final s = Some vₛ ∧ Φ vₜ vₛ.

  Inductive sim_lfp'
    (gfp: state Λₜ -> state Λₛ -> Prop) : state Λₜ -> state Λₛ-> Prop :=
  | BothFinal : ∀ t s,
    is_final t s -> sim_lfp' gfp t s

  | SourceStuck : ∀ t s,
    stuck Pₛ s -> sim_lfp' gfp t s

  | TargetStutter : ∀ t s s',
    Pₛ ⊨ s ->> s' -> sim_lfp' gfp t s' -> sim_lfp' gfp t s

  | TargetSteps : ∀ t s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> sim_lfp' gfp t' s) ->
    sim_lfp' gfp t s

  | BothSteps : ∀ t s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ s', Pₛ ⊨ s ->> s' ∧ gfp t' s') ->
    sim_lfp' gfp t s.

  Instance sim_lfp'_proper : Proper (leq ==> leq) sim_lfp'.
  Proof.
    intros gfp gfp' Hgfp s t H. induction H as [ | | | | ? ? ? H ];
      try (econstructor; eassumption || now apply Hlfp).
    apply BothSteps; eauto. intros t' Hstep.
    destruct (H _ Hstep) as (? & ? & ?).
    eexists. split; eassumption || now apply Hgfp.
  Qed.

  Definition sim_lfp : mon (state Λₜ -> state Λₛ -> Prop) := {| body := sim_lfp' |}.

  Definition sim := gfp sim_lfp.

  Lemma sim_unroll t s :
    gfp sim_lfp t s -> sim_lfp' (gfp sim_lfp) t s.
  Proof. apply (gfp_fp sim_lfp). Qed.

  Lemma sim_roll t s :
    sim_lfp' (gfp sim_lfp) t s -> gfp sim_lfp t s.
  Proof. apply (gfp_fp sim_lfp). Qed.
End SimDef.
