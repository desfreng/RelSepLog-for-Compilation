From RSL Require Import Prelude.
From RSL Require Export Commons.Memory.

Section lang_mixin.
  Context {prog pstate value : Type}.

  Context (step_rel : prog -> (pstate * memory) -> (pstate * memory) -> Prop).
  Context (is_final : (pstate * memory) -> option (value * memory)).

  Record LangMixin := {
      mixin_final_no_step:
      ∀ s v m,
        is_final s = Some (v, m) ->
        ∀ p s', ~step_rel p s s';
    }.
End lang_mixin.

Structure lang :=
  Lang
    {
      prog : Type;
      pstate : Type;
      value : Type;

      step_rel : prog -> (pstate * memory) -> (pstate * memory) -> Prop;
      is_final : (pstate * memory) -> option (value * memory);

      lang_mixin : LangMixin step_rel is_final;
    }.

Arguments step_rel {_} _ _ _.
Arguments is_final {_} _.

Notation "P ⊨ s '->>' t" := (step_rel P s t) (at level 60, right associativity).
Notation "P ⊨ s '-{' n '}>' t" := (nsteps (step_rel P) n s t) (at level 60, right associativity).
Notation "P ⊨ s '->>*' t" := (rtc (step_rel P) s t) (at level 60, right associativity).
Notation "P ⊨ s '->>+' t" := (psteps (step_rel P) s t) (at level 60, right associativity).

Definition state (Λ: lang) : Type := pstate Λ * memory.

Definition pstate_of_state {Λ : lang} : state Λ -> pstate Λ := fst.
Definition memory_of_state {Λ : lang} : state Λ -> memory := snd.

Section LangProp.
  Context {Λ: lang} (P: prog Λ).

  Lemma final_no_step s:
    is_Some (is_final s) -> ∀ t, ~(P ⊨ s ->> t).
  Proof using Type.
    intros [[] Hf] t. eapply mixin_final_no_step.
    - apply lang_mixin.
    - exact Hf.
  Qed.

  Definition can_progress (s: state Λ): Prop :=
    ∃ t, P ⊨ s ->> t.

  Definition stuck (s: state Λ) : Prop :=
    is_final s = None ∧ ~ can_progress s.

  Lemma can_progress_must_step s:
    can_progress s -> ∃ t, P ⊨ s ->> t.
  Proof using Type. easy. Qed.

  Lemma final_no_progress s:
    is_Some (is_final s) -> ~can_progress s.
  Proof using Type.
    intros [[] Hfin] Hp. destruct (can_progress_must_step _ Hp) as (? & H).
    eapply mixin_final_no_step.
    - apply lang_mixin.
    - eassumption.
    - exact H.
  Qed.

  Lemma final_not_stuck s:
    is_Some (is_final s) -> ~ stuck s.
  Proof using Type.
    intros [[] Hfin] [Hnstuck _]. congruence.
  Qed.

  Lemma progress_not_stuck s:
    can_progress s -> ~ stuck s.
  Proof using Type. intros H [_ Hnprog]. by eapply Hnprog. Qed.
End LangProp.

Section TwoProg.
  Context {Λₜ Λₛ: lang}.
  Context (Pₜ : prog Λₜ) (Pₛ : prog Λₛ).

  Abbreviation post := (value Λₜ * memory -> value Λₛ * memory -> Prop).

  Definition both_final (ϕ: post) (t: state Λₜ) (s: state Λₛ) : Prop :=
    ∃ vt vs,
      is_final t = Some vt ∧
      is_final s = Some vs ∧
      ϕ vt vs.

End TwoProg.

Ltac langmixin :=
  match goal with
  | [ Hf: is_final ?s = Some _, Hp: can_progress _ ?s |- _ ] =>
      exfalso; now apply (final_no_progress _ _ (mk_is_Some _ _ Hf) Hp)
  | [ Hf: is_final ?s = Some _, Hs: _ ⊨ ?s ->> _ |- _ ] =>
      exfalso; now apply (final_no_step _ _ (mk_is_Some _ _ Hf) _ Hs)
  | [ Hf: is_final ?s = Some _, Hs: stuck _ ?s |- _ ] =>
      exfalso; now apply (final_not_stuck _ _ (mk_is_Some _ _ Hf) Hs)
  | [ Hs: stuck ?P ?s, Hp: can_progress ?P ?s |- _ ] =>
      exfalso; now apply (progress_not_stuck _ _ Hp Hs)
  | [ Hfin: both_final _ _ _ |- _ ] =>
      destruct Hfin as (? & ? & ? & ? & ?); now langmixin
  end.
