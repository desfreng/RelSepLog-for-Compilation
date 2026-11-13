From RSL Require Import Prelude.

From RSL.Language Require Export Memory Values.

Section lang_mixin.
  Context {genv state value: Type}.

  Context (step : genv -> (state * memory) -> (state * memory) -> Prop).
  Context (is_value : state -> option value).

  Record LangMixin := {
      mixin_final_no_step s v:
        is_value s = Some v -> ∀ g m c, ~step g (s, m) c;
    }.
End lang_mixin.

Structure lang :=
  Lang
    {
      genv : Type;
      state : Type;
      value : Type;

      step : genv -> (state * memory) -> (state * memory) -> Prop;
      is_value : state -> option value;

      lang_mixin : LangMixin step is_value;
    }.

Arguments step {_} _ _ _.
Arguments is_value {_} _.

Definition config (Λ: lang) : Type := state Λ * memory.

Definition step_rel (Λ: lang) : Type :=
  genv Λ -> config Λ -> config Λ -> Prop.

Definition is_final {Λ : lang} (s: config Λ) :=
  let '(ps, m) := s in
  match is_value ps with
  | Some v => Some (v, m)
  | None => None
  end.

Lemma is_final_Some {Λ : lang} (c: config Λ) (v: value Λ) (m : memory) :
  is_final c = Some (v, m) <-> ∃ s, c = (s, m) ∧ is_value s = Some v.
Proof using Type.
  split.
  - destruct c as [s ?]. simpl.
    destruct (is_value s) eqn:Hp; intros H; inv H.
    eexists. by split.
  - intros (s & -> & Hfin). simpl. by rewrite Hfin.
Qed.

Lemma is_final_None {Λ : lang} (c: config Λ) :
  is_final c = None <-> ∃ s m, c = (s, m) ∧ is_value s = None.
Proof using Type.
  split.
  - destruct c as [s m]. simpl.
    destruct (is_value s) eqn:Hp; intros H; inv H.
    eexists s, m. by split.
  - intros (s & m & -> & Hfin). simpl. by rewrite Hfin.
Qed.
