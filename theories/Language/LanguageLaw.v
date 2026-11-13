From RSL Require Import Prelude.

From RSL.Language Require Import LanguageDef Closures.

Section LangProp.
  Context {Λ: lang} (E: genv Λ).
  Implicit Types (c : config Λ) (v : value Λ) (s: state Λ).

  Lemma final_no_step c c':
    is_Some (is_final c) -> ~(E ⊨ c ->> c').
  Proof using Type.
    intros [[] (? & -> & ?)%is_final_Some] Hs.
    eapply mixin_final_no_step.
    - apply lang_mixin.
    - done.
    - done.
  Qed.

  Definition can_progress c: Prop := ∃ c', E ⊨ c ->> c'.

  Definition stuck c : Prop := is_final c = None ∧ ~ can_progress c.

  Lemma can_progress_must_step c:
    can_progress c -> ∃ c', E ⊨ c ->> c'.
  Proof using Type. easy. Qed.

  Lemma final_no_progress c:
    is_Some (is_final c) -> ~can_progress c.
  Proof using Type.
    intros Hfin Hp.
    destruct (can_progress_must_step _ Hp) as (? & H).
    by eapply final_no_step.
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

  Definition super_stuck (c: config Λ) : Prop :=
    let '(s, m) := c in
    is_value s = None ∧ ∀ mm, m ##ₘ mm -> ~can_progress (s, m ∪ mm).

  Lemma super_stuck_is_stuck c:
    super_stuck c -> stuck c.
  Proof using Type.
    destruct c as [s m].
    intros [Hval Hnprog].
    split.
    - apply is_final_None. by eexists _, _.
    - intros H. apply Hnprog with ∅.
      + solve_map_disjoint.
      + unfold memory. by rewrite map_union_empty.
  Qed.

  Lemma super_stuck_mono s m mm:
    m ##ₘ mm ->
    super_stuck (s, m) ->
    super_stuck (s, m ∪ mm).
  Proof using Type.
    intros ? [Hval Hnprog].
    split; first done.
    intros mm' ? Hprog.
    unfold memory in *.
    rewrite <-map_union_assoc in Hprog.
    eapply Hnprog; last done.
    solve_map_disjoint.
  Qed.
End LangProp.

Abbreviation post Λt Λs := (value Λt -> value Λs -> memory -> memory -> Prop).

Definition both_final {Λt Λs: lang} (ϕ: post Λt Λs) t s : Prop :=
  ∃ vt vs mt ms,
    is_final t = Some (vt, mt) ∧
    is_final s = Some (vs, ms) ∧
    ϕ vt vs mt ms.

Definition compose_post {Λt Λm Λs: lang} (ϕ: post Λt Λm) (ψ: post Λm Λs) : post Λt Λs :=
  fun vt vs mt ms =>
    ∃ vm mm, ϕ vt vm mt mm ∧ ψ vm vs mm ms.

Lemma compose_final  {Λt Λm Λs: lang} (ϕ: post Λt Λm) (ψ: post Λm Λs) t m s :
  both_final ϕ t m ->
  both_final ψ m s ->
  both_final (compose_post ϕ ψ) t s.
Proof.
  intros (vt & vm & mt & mm & Ht & Hm & Hϕ).
  intros (? & vs & ? & ms & Heq & Hs & Hψ).
  inv Heq.
  exists vt, vs, mt, ms. split_and!.
  - done.
  - done.
  - by exists vm, mm.
Qed.

Ltac langmixin :=
  match goal with
  | [ Hf: is_final ?s = Some _, Hp: can_progress _ ?s |- _ ] =>
      exfalso; now apply (final_no_progress _ _ (mk_is_Some _ _ Hf) Hp)

  | [ Hf: is_final ?s = Some _, Hs: _ ⊨ ?s ->> _ |- _ ] =>
      exfalso; now apply (final_no_step _ _ _ (mk_is_Some _ _ Hf) Hs)

  | [ Hf: is_final ?s = Some _, Hs: stuck _ ?s |- _ ] =>
      exfalso; now apply (final_not_stuck _ _ (mk_is_Some _ _ Hf) Hs)

  | [ Hs: stuck ?P ?s, Hp: can_progress ?P ?s |- _ ] =>
      exfalso; now apply (progress_not_stuck _ _ Hp Hs)

  | [ Hfin: both_final _ _ _ |- _ ] =>
      destruct Hfin as (? & ? & ? & ? & ? & ? & ?); now langmixin

  | [ Hss: super_stuck _ _ |- _ ] =>
      apply super_stuck_is_stuck in Hss; now langmixin

  end.
