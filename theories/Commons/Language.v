From RSL Require Import Prelude.

From RSL.Commons Require Export Memory Values.

Section lang_mixin.
  Context {prog istate value : Type}.

  Context (step_rel : prog -> (istate * memory) -> (istate * memory) -> Prop).
  Context (is_value : istate -> option value).

  Record LangMixin := {
      mixin_final_no_step s v:
        is_value s = Some v -> ∀ m p s', ~step_rel p (s, m) s';

      mixin_can_step_mono p s m t mm:
        step_rel p (s, m) t ->
        (∃ t', step_rel p (s, m ∪ mm) t')
    }.
End lang_mixin.

Structure lang :=
  Lang
    {
      prog : Type;
      istate : Type;
      value : Type;

      step_rel : prog -> (istate * memory) -> (istate * memory) -> Prop;
      is_value : istate -> option value;

      lang_mixin : LangMixin step_rel is_value;
    }.

Arguments step_rel {_} _ _ _.
Arguments is_value {_} _.

Notation "P ⊨ s '->>' t" := (step_rel P s t) (at level 60, right associativity).
Notation "P ⊨ s '-{' n '}>' t" := (nsteps (step_rel P) n s t) (at level 60, right associativity).
Notation "P ⊨ s '->>*' t" := (rtc (step_rel P) s t) (at level 60, right associativity).
Notation "P ⊨ s '->>+' t" := (psteps (step_rel P) s t) (at level 60, right associativity).

Definition state (Λ: lang) : Type := istate Λ * memory.

Definition is_final {Λ : lang} (s: state Λ) :=
  let '(ps, m) := s in
  match is_value ps with
  | Some v => Some (v, m)
  | None => None
  end.

Section LangProp.
  Context {Λ: lang} (P: prog Λ).
  Implicit Types (s : state Λ) (v : value Λ) (ss: istate Λ).

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

  Lemma progress_not_final s:
    can_progress s -> is_final s = None.
  Proof using Type.
    intros (s' & ?)%can_progress_must_step.
    destruct (is_final s) eqn:Hfin; auto.
    exfalso.
    by eapply final_no_step.
  Qed.

  Lemma is_final_mem_ignore ss m m1 m2 v :
    is_final (ss, m1) = Some (v, m) ->
    is_final (ss, m2) = Some (v, m2).
  Proof using Type.
    intros (? & He & Hfin)%is_final_Some.
    inv He. simpl. by rewrite Hfin.
  Qed.

  Lemma is_final_mem_same ss m m' v :
    is_final (ss, m) = Some (v, m') ->
    m = m'.
  Proof using Type.
    intros (? & He & Hfin)%is_final_Some. by inv He.
  Qed.

  Lemma can_progress_mono ss m mm:
    can_progress (ss, m) ->
    can_progress (ss, m ∪ mm).
  Proof using Type.
    intros (t & Hstep).
    eapply (mixin_can_step_mono _ _ (lang_mixin Λ)) in Hstep as (t' & Hstep).
    by eexists.
  Qed.

  Lemma stuck_anti_mono ss m mm:
    stuck (ss, m ∪ mm) ->
    stuck (ss, m).
  Proof using Type.
    intros [(? & ? & Heq & Hval)%is_final_None Hnprog].
    split.
    - inv Heq. apply is_final_None. by eexists _, _.
    - intro Hp. apply Hnprog, can_progress_mono, Hp.
  Qed.

  Definition super_stuck '(ss, m) :=
    is_value ss = None ∧ ∀ mm, ~can_progress (ss, m ∪ mm).

  Lemma super_stuck_is_stuck s :
    super_stuck s -> stuck s.
  Proof using Type.
    destruct s as [ss m].
    intros [Hval Hnprog].
    split.
    - apply is_final_None. by eexists _, _.
    - intros H. apply Hnprog with ∅.
      unfold memory. by rewrite map_union_empty.
  Qed.

  Lemma super_stuck_mono ss m mm:
    super_stuck (ss, m) ->
    super_stuck (ss, m ∪ mm).
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

  Definition both_final ϕ (t: state Λt) (s: state Λs) : Prop :=
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
