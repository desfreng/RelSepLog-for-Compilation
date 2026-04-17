From stdpp Require Import prelude.
From stdpp Require Import tactics.

From Coinduction Require Import all.

From RSL Require Import RTL.
From RSL Require Import Semantics.
From RSL Require Import SemanticsSpec.
From RSL Require Import Refinement.

(* Set Mangle Names. *)

Section Sim.
  Context (stepₜ stepₛ: state -> state -> Prop).

  Context (Φ: observation).

  Variant final : state -> state -> Prop :=
  | FinalState : ∀ vₜ mₜ vₛ mₛ,
    Φ (vₜ, mₜ) (vₛ, mₛ) ->
    final ([], ReturnState vₜ, mₜ) ([], ReturnState vₛ, mₛ).

  Inductive sim_lfp' (gfp: state -> state -> Prop) : state ->  state -> Prop :=
  | BothFinal : ∀ t s,
    final t s -> sim_lfp' gfp t s

  | SourceStuck : ∀ t s,
    stuck P s -> sim_lfp' gfp t s

  | TargetStutter : ∀ t s s',
    P ⊨ s ->> s' -> sim_lfp' gfp t s' -> sim_lfp' gfp t s

  | TargetSteps : ∀ t s,
    can_progress P t ->
    (∀ t', P ⊨ t ->> t' -> sim_lfp' gfp t' s) ->
    sim_lfp' gfp t s

  | BothSteps : ∀ t s,
    can_progress P t ->
    (∀ t', P ⊨ t ->> t' -> ∃ s', P ⊨ s ->> s' ∧ gfp t' s') ->
    sim_lfp' gfp t s.

  Instance sim_lfp'_proper : Proper (leq ==> leq) sim_lfp'.
  Proof.
    intros gfp gfp' Hgfp s t H. induction H as [ | | | | ? ? ? H ];
      try (econstructor; eassumption || now apply Hlfp).
    apply BothSteps; eauto. intros t' Hstep.
    destruct (H _ Hstep) as (? & ? & ?).
    eexists. split; eassumption || now apply Hgfp.
  Qed.

  Definition sim_lfp : mon (state -> state -> Prop) := {| body := sim_lfp' |}.

  Definition sim := gfp sim_lfp.

  Lemma sim_coind (R : state -> state -> Prop) :
    (∀ t s, R t s -> sim_lfp R t s) ->
    ∀ t s, R t s -> sim t s.
  Proof.
    intros Hstep. unfold sim.
    coinduction Re cih. intros t s HR.
    assert (HRe: R <= elem Re). {
      intros t' s' HR'. now apply cih.
    }
    apply (sim_lfp'_proper R _ HRe).
    now apply Hstep.
  Qed.

  Lemma sim_stuck_example t s :
    stuck P t -> stuck P s -> sim t s.
  Proof.
    intros Ht Hs. unfold sim.
    step. apply BothStuck. all: assumption.
  Qed.
End Sim.
