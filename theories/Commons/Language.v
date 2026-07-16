From RSL Require Import Prelude.

From RSL.Commons Require Export Memory Values.

Section lang_mixin.
  Context {prog pstate value : Type}.

  Context (step_rel : prog -> (pstate * memory) -> (pstate * memory) -> Prop).
  Context (is_value : pstate -> option value).

  Record LangMixin := {
      mixin_final_no_step:
      ∀ s v,
        is_value s = Some v ->
        ∀ m p s', ~step_rel p (s, m) s';
    }.
End lang_mixin.

Structure lang :=
  Lang
    {
      prog : Type;
      pstate : Type;
      value : Type;

      step_rel : prog -> (pstate * memory) -> (pstate * memory) -> Prop;
      is_value : pstate -> option value;

      lang_mixin : LangMixin step_rel is_value;
    }.

Arguments step_rel {_} _ _ _.
Arguments is_value {_} _.

Notation "P ⊨ s '->>' t" := (step_rel P s t) (at level 60, right associativity).
Notation "P ⊨ s '-{' n '}>' t" := (nsteps (step_rel P) n s t) (at level 60, right associativity).
Notation "P ⊨ s '->>*' t" := (rtc (step_rel P) s t) (at level 60, right associativity).
Notation "P ⊨ s '->>+' t" := (psteps (step_rel P) s t) (at level 60, right associativity).

Definition state (Λ: lang) : Type := pstate Λ * memory.

Definition pstate_of_state {Λ : lang} : state Λ -> pstate Λ := fst.
Definition memory_of_state {Λ : lang} : state Λ -> memory := snd.

Definition is_final {Λ : lang} (s: state Λ) :=
  let '(ps, m) := s in
  match is_value ps with
  | Some v => Some (v, m)
  | None => None
  end.

Section LangProp.
  Context {Λ: lang} (P: prog Λ).
  Implicit Type s : state Λ.
  Implicit Type v : value Λ.

  Lemma is_final_Some s v m:
    is_final s = Some (v, m)
    <->
      ∃ ps, s = (ps, m) ∧ is_value ps = Some v.
  Proof using Type.
    split.
    - destruct s as [ps ?]. simpl.
      destruct (is_value ps) eqn:Hp; intros H; inv H.
      eexists. by split.
    - intros (ps & -> & Hfin). simpl. by rewrite Hfin.
  Qed.

  Local Lemma is_final_None s:
    is_final s = None
    <->
      ∃ ps m, s = (ps, m) ∧ is_value ps = None.
  Proof using Type.
    split.
    - destruct s as [ps m]. simpl.
      destruct (is_value ps) eqn:Hp; intros H; inv H.
      eexists ps, m. by split.
    - intros (ps & m & -> & Hfin). simpl. by rewrite Hfin.
  Qed.

  Lemma final_no_step s:
    is_Some (is_final s) -> ∀ t, ~(P ⊨ s ->> t).
  Proof using Type.
    intros [[] (ps & -> & Hfin)%is_final_Some] t.
    eapply mixin_final_no_step.
    - apply lang_mixin.
    - exact Hfin.
  Qed.

  Definition can_progress s: Prop := ∃ t, P ⊨ s ->> t.

  Definition stuck s : Prop := is_final s = None ∧ ~ can_progress s.

  Lemma can_progress_must_step s:
    can_progress s -> ∃ t, P ⊨ s ->> t.
  Proof using Type. easy. Qed.

  Lemma final_no_progress s:
    is_Some (is_final s) -> ~can_progress s.
  Proof using Type.
    intros [[] (ps & -> & Hfin)%is_final_Some] Hp.
    destruct (can_progress_must_step _ Hp) as (? & H).
    eapply mixin_final_no_step.
    - apply lang_mixin.
    - exact Hfin.
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

  Lemma is_final_mem_ignore ps m m1 m2 v :
    is_final (ps, m1) = Some (v, m) ->
    is_final (ps, m2) = Some (v, m2).
  Proof using Type.
    intros (? & He & Hfin)%is_final_Some.
    inv He. simpl. by rewrite Hfin.
  Qed.

  Lemma is_final_mem_same ps m m' v :
    is_final (ps, m) = Some (v, m') ->
    m = m'.
  Proof using Type.
    intros (? & He & Hfin)%is_final_Some. by inv He.
  Qed.
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
