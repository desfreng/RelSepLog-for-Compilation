From stdpp Require Import prelude.

From RSL Require Import Commons.Utils.

(* Set Mangle Names. *)

Section lang_mixin.
  Context {prog state value : Type}.

  Context (step_rel : prog -> state -> state -> Prop).
  Context (can_progress : prog -> state -> Prop).

  Context (is_final : state -> option value).

  Record LangMixin := {
      mixin_final_no_progress:
      ∀ p s v, is_final s = Some v -> ~can_progress p s;
      mixin_final_no_step:
      ∀ p s t v, is_final s = Some v -> ~step_rel p s t;
      mixin_can_progress_must_step:
      ∀ p s, can_progress p s -> ∃ t, step_rel p s t;
     }.
End lang_mixin.

Structure lang :=
  Lang
    {
      prog : Type;
      state : Type;
      value : Type;

      step_rel : prog -> state -> state -> Prop;

      can_progress : prog -> state -> Prop;
      is_final : state -> option value;

      lang_mixin : LangMixin step_rel can_progress is_final;
    }.

Arguments step_rel {_} _ _ _.
Arguments can_progress {_} _ _.
Arguments is_final {_} _.

Notation "P ⊨ s '->>' t" := (step_rel P s t) (at level 60, right associativity).
Notation "P ⊨ s '-{' n '}>' t" := (nsteps (step_rel P) n s t) (at level 60, right associativity).
Notation "P ⊨ s '->>*' t" := (rtc (step_rel P) s t) (at level 60, right associativity).
Notation "P ⊨ s '->>+' t" := (psteps (step_rel P) s t) (at level 60, right associativity).

Section Stuck.
  Context {Λ: lang} (P: prog Λ).

  Definition stuck (s: state Λ) : Prop :=
    is_final s = None ∧ ~ can_progress P s.

  Lemma final_not_stuck : ∀ s v,
    is_final s = Some v -> ~ stuck s.
  Proof. intros ? ? H [? ?]. inv H. Qed.

  Lemma progress_not_stuck : ∀ s,
    can_progress P s -> ~ stuck s.
  Proof. intros ? ? []. tauto. Qed.
End Stuck.

Tactic Notation "mixin" :=
  match goal with
  | [ Hf: is_final ?s = Some _, Hp: can_progress _ ?s |- _ ] =>
      exfalso;
      eapply mixin_final_no_progress;
      [apply lang_mixin | apply Hf | apply Hp]
  | [ Hf: is_final ?s = Some _, Hs: _ ⊨ ?s ->> _ |- _ ] =>
      exfalso;
      eapply mixin_final_no_step;
      [apply lang_mixin | apply Hf | apply Hs]
  | [ Hf: is_final ?s = Some _, Hs: stuck _ ?s |- _ ] =>
      let Hnfin := fresh "Hnfin" in
      destruct Hs as [Hnfin _];
      rewrite Hnfin in Hf;
      discriminate Hf
  | [ Hs: stuck ?P ?s, Hp: can_progress ?P ?s |- _ ] =>
      let Hnp := fresh "Hnp" in
      destruct Hs as [_ Hnp];
      exfalso; apply (Hnp Hp)
  end.
