From RSL Require Import Prelude.

From RSL.Commons Require Export Memory Values.

Section lang_mixin.
  Context {prog state value : Type}.

  Context (step_rel : prog -> (state * memory) -> (state * memory) -> Prop).
  Context (is_value : state -> option value).

  Record LangMixin := {
      mixin_final_no_step s v:
        is_value s = Some v -> ∀ m p s', ~step_rel p (s, m) s';

      mixin_step_mono p s m c mm:
        step_rel p (s, m) c ->
        (∃ c', step_rel p (s, m ∪ mm) c')
    }.
End lang_mixin.

Structure lang :=
  Lang
    {
      prog : Type;
      state : Type;
      value : Type;

      step_rel : prog -> (state * memory) -> (state * memory) -> Prop;
      is_value : state -> option value;

      lang_mixin : LangMixin step_rel is_value;
    }.

Arguments step_rel {_} _ _ _.
Arguments is_value {_} _.

Notation "P ⊨ s '->>' t" := (step_rel P s t) (at level 60, right associativity).
Notation "P ⊨ s '-{' n '}>' t" := (nsteps (step_rel P) n s t) (at level 60, right associativity).
Notation "P ⊨ s '->>*' t" := (rtc (step_rel P) s t) (at level 60, right associativity).
Notation "P ⊨ s '->>+' t" := (psteps (step_rel P) s t) (at level 60, right associativity).

Definition config (Λ: lang) : Type := state Λ * memory.

Definition is_final {Λ : lang} (s: config Λ) :=
  let '(ps, m) := s in
  match is_value ps with
  | Some v => Some (v, m)
  | None => None
  end.

Section LangProp.
  Context {Λ: lang} (P: prog Λ).
  Implicit Types (c : config Λ) (v : value Λ) (s: state Λ).

  Lemma is_final_Some c v m:
    is_final c = Some (v, m) <-> ∃ s, c = (s, m) ∧ is_value s = Some v.
  Proof using Type.
    split.
    - destruct c as [s ?]. simpl.
      destruct (is_value s) eqn:Hp; intros H; inv H.
      eexists. by split.
    - intros (s & -> & Hfin). simpl. by rewrite Hfin.
  Qed.

  Local Lemma is_final_None c:
    is_final c = None <-> ∃ s m, c = (s, m) ∧ is_value s = None.
  Proof using Type.
    split.
    - destruct c as [s m]. simpl.
      destruct (is_value s) eqn:Hp; intros H; inv H.
      eexists s, m. by split.
    - intros (s & m & -> & Hfin). simpl. by rewrite Hfin.
  Qed.

  Lemma final_no_step c:
    is_Some (is_final c) -> ∀ c', ~(P ⊨ c ->> c').
  Proof using Type.
    intros [[] (s & -> & Hfin)%is_final_Some] t.
    eapply mixin_final_no_step.
    - apply lang_mixin.
    - exact Hfin.
  Qed.

  Definition can_progress c: Prop := ∃ c', P ⊨ c ->> c'.

  Definition stuck c : Prop := is_final c = None ∧ ~ can_progress c.

  Lemma can_progress_must_step c:
    can_progress c -> ∃ c', P ⊨ c ->> c'.
  Proof using Type. easy. Qed.

  Lemma final_no_progress c:
    is_Some (is_final c) -> ~can_progress c.
  Proof using Type.
    intros [[] (s & -> & Hfin)%is_final_Some] Hp.
    destruct (can_progress_must_step _ Hp) as (? & H).
    eapply mixin_final_no_step.
    - apply lang_mixin.
    - exact Hfin.
    - exact H.
  Qed.

  Lemma final_not_stuck c:
    is_Some (is_final c) -> ~ stuck c.
  Proof using Type.
    intros [[] Hfin] [Hnstuck _]. congruence.
  Qed.

  Lemma progress_not_stuck c:
    can_progress c -> ~ stuck c.
  Proof using Type. intros H [_ Hnprog]. by eapply Hnprog. Qed.

  Lemma progress_not_final c:
    can_progress c -> is_final c = None.
  Proof using Type.
    intros (c' & ?)%can_progress_must_step.
    destruct (is_final c) eqn:Hfin; auto.
    exfalso.
    by eapply final_no_step.
  Qed.

  Lemma is_final_mem_ignore s m m1 m2 v :
    is_final (s, m1) = Some (v, m) ->
    is_final (s, m2) = Some (v, m2).
  Proof using Type.
    intros (? & He & Hfin)%is_final_Some.
    inv He. simpl. by rewrite Hfin.
  Qed.

  Lemma is_final_mem_same s m m' v :
    is_final (s, m) = Some (v, m') ->
    m = m'.
  Proof using Type.
    intros (? & He & Hfin)%is_final_Some. by inv He.
  Qed.

  Lemma can_progress_mono s m mm:
    can_progress (s, m) ->
    can_progress (s, m ∪ mm).
  Proof using Type.
    intros (t & Hstep).
    eapply (mixin_step_mono _ _ (lang_mixin Λ)) in Hstep as (t' & Hstep).
    by eexists.
  Qed.

  Lemma stuck_anti_mono s m mm:
    stuck (s, m ∪ mm) ->
    stuck (s, m).
  Proof using Type.
    intros [(? & ? & Heq & Hval)%is_final_None Hnprog].
    split.
    - inv Heq. apply is_final_None. by eexists _, _.
    - intro Hp. apply Hnprog, can_progress_mono, Hp.
  Qed.

  Definition super_stuck (c: config Λ) : Prop :=
    let '(s, m) := c in
    is_value s = None ∧ ∀ mm, ~can_progress (s, m ∪ mm).

  Lemma super_stuck_is_stuck c:
    super_stuck c -> stuck c.
  Proof using Type.
    destruct c as [s m].
    intros [Hval Hnprog].
    split.
    - apply is_final_None. by eexists _, _.
    - intros H. apply Hnprog with ∅.
      unfold memory. by rewrite map_union_empty.
  Qed.

  Lemma super_stuck_mono s m mm:
    super_stuck (s, m) ->
    super_stuck (s, m ∪ mm).
  Proof using Type.
    intros [Hval Hnprog].
    split; first done.
    intros mm' Hprog.
    unfold memory in *.
    rewrite <-map_union_assoc in Hprog.
    by eapply Hnprog.
  Qed.
End LangProp.

Section TwoProg.
  Context {Λt Λs: lang}.
  Context (Pt : prog Λt) (Ps : prog Λs).

  Definition both_final ϕ (t: config Λt) (s: config Λs) : Prop :=
    ∃ vt vs mt ms,
      is_final t = Some (vt, mt) ∧
      is_final s = Some (vs, ms) ∧
      ϕ vt vs mt ms.

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
      destruct Hfin as (? & ? & ? & ? & ? & ? & ?); now langmixin
  end.
