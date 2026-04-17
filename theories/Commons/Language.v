From stdpp Require Import prelude.

Section language_mixin.
  Context {state value : Type}.

  Context (step : state -> state -> Prop).

  Context (can_progress : state -> Prop).
  Context (is_final : state -> option value).

  Record LanguageMixin := {
      mixin_final_no_progress : ∀ s v, is_final s = Some v -> can_progress s -> False;
      mixin_can_progress_must_step : ∀ s, can_progress s -> ∃ t, step s t;
    }.
End language_mixin.

Structure language :=
  Language {
      state : Type;
      value : Type;

      step : state -> state -> Prop;

      can_progress : state -> Prop;
      is_final : state -> option value;

      language_mixin : LanguageMixin step can_progress is_final;
    }.

Arguments step {_} _ _.
Arguments can_progress {_} _.
Arguments is_final {_}.

Section Language.
  Context {Λ: language}.

  Definition stuck (s : state Λ) : Prop :=
    is_final s = None ∧ ~ can_progress s.

  Lemma final_not_stuck : ∀ s v,
    is_final s = Some v -> ~ stuck s.
  Proof. intros ? ? H [? ?]. inv H. Qed.

  Lemma progress_not_stuck : ∀ s,
    can_progress s -> ~ stuck s.
  Proof. intros ? ? []. tauto. Qed.

End Language.
