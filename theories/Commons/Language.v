From stdpp Require Import prelude.

From RSL Require Import Commons.Utils.

(* Set Mangle Names. *)

Section lang_mixin.
  Context {prog state value : Type}.

  Context (step_rel : prog -> state -> state -> Prop).
  Context (is_final : state -> option value).

  Record LangMixin := {
      mixin_final_no_step:
      ∀ p s t v, is_final s = Some v -> ~step_rel p s t;
     }.
End lang_mixin.

Structure lang :=
  Lang
    {
      prog : Type;
      state : Type;
      value : Type;

      step_rel : prog -> state -> state -> Prop;
      is_final : state -> option value;

      lang_mixin : LangMixin step_rel is_final;
    }.

Arguments step_rel {_} _ _ _.
Arguments is_final {_} _.

Notation "P ⊨ s '->>' t" := (step_rel P s t) (at level 60, right associativity).
Notation "P ⊨ s '-{' n '}>' t" := (nsteps (step_rel P) n s t) (at level 60, right associativity).
Notation "P ⊨ s '->>*' t" := (rtc (step_rel P) s t) (at level 60, right associativity).
Notation "P ⊨ s '->>+' t" := (psteps (step_rel P) s t) (at level 60, right associativity).

Section LangProp.
  Context {Λ: lang} (P: prog Λ).

  Definition can_progress (s: state Λ) : Prop :=
    ∃ t, P ⊨ s ->> t.

  Definition stuck (s: state Λ) : Prop :=
    is_final s = None ∧ ~ can_progress s.

  Lemma final_no_step:
    ∀ s v, is_final s = Some v -> ∀ t, ~(P ⊨ s ->> t).
  Proof.
    intros s v Hf t. eapply mixin_final_no_step.
    - apply lang_mixin.
    - exact Hf.
  Qed.

  Lemma can_progress_must_step:
    ∀ s, can_progress s -> ∃ t, P ⊨ s ->> t.
  Proof. easy. Qed.

  Lemma final_no_progress:
    ∀ s v, is_final s = Some v -> ~can_progress s.
  Proof.
    intros s v Hfin Hp. destruct (can_progress_must_step _ Hp) as [? H].
    eapply mixin_final_no_step.
    - apply lang_mixin.
    - eassumption.
    - exact H.
  Qed.

  Lemma final_not_stuck : ∀ s v,
    is_final s = Some v -> ~ stuck s.
  Proof. intros ? ? H [? ?]. inv H. Qed.

  Lemma progress_not_stuck : ∀ s,
    can_progress s -> ~ stuck s.
  Proof. intros ? ? []. tauto. Qed.
End LangProp.

Tactic Notation "mixin" :=
  match goal with
  | [ Hf: is_final ?s = Some _, Hp: can_progress _ ?s |- _ ] =>
      exfalso; now apply (final_no_progress _ _ _ Hf Hp)
  | [ Hf: is_final ?s = Some _, Hs: _ ⊨ ?s ->> _ |- _ ] =>
      exfalso; now apply (final_no_step _ _ _ Hf _ Hs)
  | [ Hf: is_final ?s = Some _, Hs: stuck _ ?s |- _ ] =>
      exfalso; now apply (final_not_stuck _ _ _ Hf Hs)
  | [ Hs: stuck ?P ?s, Hp: can_progress ?P ?s |- _ ] =>
      exfalso; now apply (progress_not_stuck _ _ Hp Hs)
  end.

(* Lemma LPO {T: Type} : ∀ (P: T -> Prop), *)
(*   (∀ x, Decision (P x)) -> *)
(*   (∃ x, P x) ∨ (∀ x, ~ P x). *)
