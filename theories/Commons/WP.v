From stdpp Require Import prelude.
From stdpp Require Import strings.

From RSL Require Import Commons.Language.
From RSL Require Import Commons.Utils.

(* Set Mangle Names. *)

Section WPProp.
  Context {Λ: lang} (P: prog Λ).

  Implicit Type s : state Λ.

  Definition final_with Q s : Prop := ∃ v, is_final s = Some v ∧ Q v.

  (** [safe Q n s] : s is a state that is safe for at most n steps:
      - s is a final step or
      - s is not stuck and can do at most n steps. *)
  Inductive safe Q : state Λ -> nat -> Prop :=
  | safe_init : ∀ s, safe Q s 0
  | final_is_safe : ∀ s n, final_with Q s -> safe Q s n
  | safe_to_step : ∀ s n,
    (* I am not stuck *)
    can_progress P s ->
    (* All possible next states are safe for at most n least *)
    (∀ t, P ⊨ s ->> t -> safe Q t n) ->
    (* I am safe for at most n+1 least *)
    safe Q s (S n).

  Lemma safe_from_progress Q s n :
    (∀ t m, m < n -> P ⊨ s -{m}> t -> final_with Q t ∨ can_progress P t) ->
    safe Q s n.
  Proof.
    induction n as [ | n IH] in s |- *; intros H.
    - constructor.
    - assert (Hstep: P ⊨ s -{0}> s) by constructor.
      assert (Hle: 0 < S n) by lia.
      destruct (H _ _ Hle Hstep) as [Hfin | Hns]; clear Hstep Hle.
      + now constructor.
      + apply safe_to_step; auto. intros t Hstep.
        apply IH. intros u m Heq Hsteps. subst.
        apply H with (S m).
        * lia.
        * econstructor; now eauto.
  Qed.

  Lemma safe_implies_progress Q s n :
    safe Q s n ->
    ∀ t m, m < n -> P ⊨ s -{m}> t -> final_with Q t ∨ can_progress P t.
  Proof.
    intros Hsafe.
    induction Hsafe as [s' | s' n' Hfin | s' n' Hns Hsafe IH]
      in n, Hsafe |- *; intros t m Hlt Hrtc.
    - inv Hlt.
    - destruct m as [ | m].
      + inv Hrtc. now left.
      + exfalso.
        destruct Hfin as (v & Hfin & HQ). apply nsteps_inv_l in Hrtc.
        destruct Hrtc as (? & Hstep & ?).
        eapply mixin_final_no_step; eauto. apply lang_mixin.
    - destruct m as [ | m ].
      + inv Hrtc; now auto.
      + apply nsteps_inv_l in Hrtc.
        destruct Hrtc as (u & Hstep & Hrtc).
        eapply IH; try eassumption; lia.
  Qed.

  Definition safe_mono Q s :
    ∀ n m, m <= n -> safe Q s n -> safe Q s m.
  Proof.
    intros n m Hle Hsafe.
    induction Hsafe as [ | | ? ? Hns Hsafe IH ] in m, Hle |- *.
    - inv Hle. constructor.
    - now apply final_is_safe.
    - destruct m as [ | m ].
      + constructor.
      + apply safe_to_step.
        * assumption.
        * intros ? Ht. apply IH; auto. lia.
  Qed.
End WPProp.
