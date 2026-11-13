From RSL Require Import Prelude.

From RSL.Language Require Import Language.

From Stdlib Require Import Classical.

From Coinduction Require Import all.

Section Behavior.
  Context {Λ: lang} (E: genv Λ).
  Implicit Types s : config Λ.

  Program Definition diverges_: mon (config Λ -> Prop) :=
    {| body R s := ∃ s', E ⊨ s ->> s' ∧ R s' |}.
  Next Obligation. firstorder. Qed.

  Definition diverges : config Λ -> Prop := gfp diverges_.

  Lemma diveges_sound f:
    (∀ n, E ⊨ f n ->> f (S n)) -> diverges (f 0).
  Proof using Type.
    intros Hf. cut (∀ n, diverges (f n)); auto.
    unfold diverges. coinduction R cih.
    intros n. exists (f (S n)); auto.
  Qed.

  Lemma diverges_unroll t:
    diverges t -> ∃ t', E ⊨ t ->> t' ∧ diverges t'.
  Proof using Type.
    intros H. unfold diverges in H. apply (gfp_fp diverges_) in H.
    inv H. eexists; now eauto.
  Qed.

  Lemma diverges_roll t:
    (∃ t', E ⊨ t ->> t' ∧ diverges t') -> diverges t.
  Proof using Type.
    intros (t' & Hstep & Hdiv).
    apply (gfp_fp diverges_). by econstructor.
  Qed.

  Lemma diverge_iff t :
    diverges t <-> (∃ t', E ⊨ t ->> t' ∧ diverges t').
  Proof using Type.
    split.
    - by apply diverges_unroll.
    - by apply diverges_roll.
  Qed.

  Definition strong_diverge (t: config Λ) : Prop :=
    ∀ t', E ⊨ t ->>* t' -> can_progress E t'.

  Lemma strong_div_always_div t :
    strong_diverge t ->
    ∀ t', E ⊨ t ->>* t' -> diverges t'.
  Proof using Type.
    unfold diverges.
    coinduction C CIH.
    intros H t' Hrtc.
    assert (can_progress E t') as (u & Hstep) by now apply H.
    exists u. split; first done.
    apply CIH; first done.
    by eapply steps_r.
  Qed.

  Variant behavior :=
  | Terminating (v: value Λ) (m: memory)
  | Diverging
  | Undef.

  (* [beh s] is the set of all the behaviors of [s] *)
  Inductive beh : behavior -> config Λ -> Prop :=
  | IsTerminating : ∀ s v m,
      is_final s = Some (v, m) ->
      beh (Terminating v m) s
  | IsDiverging : ∀ s,
      diverges s ->
      beh Diverging s
  | IsStuck : ∀ s,
      stuck E s ->
      beh Undef s
  | IsSteping : ∀ s t b,
      beh b t ->
      E ⊨ s ->> t ->
      beh b s.

  Global Instance beh_elem_config : ElemOf behavior (config Λ) := beh.

  (* [s] is terminating iff there is a execution from [s] to a final state. *)
  Lemma has_terminating_behavior : ∀ s v m,
    Terminating v m ∈ s <-> ∃ s', E ⊨ s ->>* s' ∧ is_final s' = Some (v, m).
  Proof using Type.
    intros s v m. split; intros Hbeh.
    - remember (Terminating v m) as b eqn:Hb.
      induction Hbeh as [ s | | | s t b ? IH Hstep ]; inv Hb; auto.
      + exists s. split; auto using steps_refl.
      + destruct (IH eq_refl) as (s' & Hrtc & Hfin). clear IH.
        exists s'. split; eauto. by eapply steps_l; eauto.
    - destruct Hbeh as (s' & Hrtc & Hfin).
      induction Hrtc as [ | s ? u Hstep Hrtc IH ].
      + now constructor.
      + eapply IsSteping; eauto. now apply IH.
  Qed.

  (* [s] is diverging iff [s] has a diverging execution *)
  Lemma has_diverging_behavior : ∀ s,
    Diverging ∈ s <-> diverges s.
  Proof using Type.
    intros s. split; intros Hbeh.
    - revert s Hbeh. unfold diverges. coinduction R cih.
      intros s Hbeh. inv Hbeh as [ | ? Hdiv | | ? t ? H Hstep ].
      + apply (gfp_pfp diverges_) in Hdiv.
        destruct Hdiv as (s' & Hstep & Hdiv).
        exists s'. split; auto. apply cih. apply IsDiverging. assumption.
      + exists t. split; auto.
    - now apply IsDiverging.
  Qed.

  (* [s] has a undef behavior if [s] reduces to a stuck state. *)
  Lemma has_undef_behavior : ∀ s,
    Undef ∈ s <-> ∃ t, E ⊨ s ->>* t ∧ stuck E t.
  Proof using Type.
    intros s. split; intros Hbeh.
    - remember Undef as b eqn:Hb.
      induction Hbeh as [ | | s | s t b ? IH Hstep ]; inv Hb; auto.
      + exists s. now split.
      + destruct (IH eq_refl) as (u & Hrtc & Hstuck).
        exists u. split.
        * now apply steps_l with t.
        * assumption.
    - destruct Hbeh as (u & Hrtc & Hstuck).
      induction Hrtc  as [ | s t ? Hstep Hrtc IH].
      + now constructor.
      + eapply IsSteping.
        * now apply IH.
        * easy.
  Qed.

  Definition does_end s : Prop :=
    ∃ t, E ⊨ s ->>* t ∧ (is_Some (is_final t) ∨ stuck E t).

  Lemma not_ending_diverges:
    ∀ s, ~(does_end s) -> ∀ t, E ⊨ s ->>* t -> diverges t.
  Proof using Type.
    intros s H. unfold diverges.
    coinduction R cih.
    assert (Hs: ∀ t, E ⊨ s ->>* t -> is_final t = None ∧ ~ stuck E t).
    {
      intros t Hstep. apply not_ex_all_not with (n := t) in H.
      split.
      - destruct (is_final t) as [v | ].
        + exfalso. apply H. split; auto.
        + reflexivity.
      - intro Hs. apply H. now auto.
    }
    intros t Hrtc.
    destruct (Hs t) as [Hnfin Hnstuck]; auto.
    unfold stuck in Hnstuck.
    destruct (classic (can_progress E t)) as [Hprog | HnProg].
    - destruct (can_progress_must_step _ _ Hprog) as [u Hstep].
      exists u. split; auto.
      apply cih. eapply steps_r; eassumption.
    - exfalso. apply Hnstuck. split; auto.
  Qed.

  Theorem every_state_has_beh : ∀ s, ∃ b, b ∈ s.
  Proof using Type.
    intros s. destruct (classic (does_end s)) as [(t & Hrtc & [Hfin | H]) | H].
    - destruct Hfin as [[v m] Hfin].
      exists (Terminating v m). apply has_terminating_behavior.
      exists t; auto.
    - exists Undef. apply has_undef_behavior.
      exists t; auto.
    - exists Diverging. apply has_diverging_behavior.
      apply not_ending_diverges with s; auto.
  Qed.
End Behavior.

Section Refinement.
  Context {Λt Λs: lang}.
  Context (Et: genv Λt) (Es: genv Λs).

  Instance beht_elem : ElemOf behavior (config Λt) := beh Et.
  Instance behs_elem : ElemOf behavior (config Λs) := beh Es.

  Variant behavior_order ϕ : @behavior Λt -> @behavior Λs -> Prop :=
  | BehOrderTerm vt vs mt ms :
      ϕ vt vs mt ms -> behavior_order ϕ (Terminating vt mt) (Terminating vs ms)
  | BehOrderDiv :
      behavior_order ϕ Diverging Diverging
  | BehOrderUndef bt :
      behavior_order ϕ bt Undef.

  Variant behavior_equal ϕ : @behavior Λt -> @behavior Λs -> Prop :=
  | BehEqTerm vt vs mt ms :
      ϕ vt vs mt ms -> behavior_equal ϕ (Terminating vt mt) (Terminating vs ms)
  | BehEqDiv :
      behavior_equal ϕ Diverging Diverging
  | BehEqUndef :
      behavior_equal ϕ Undef Undef.

  Notation "a '⊑{' ϕ '}' b" :=
    (behavior_order ϕ a b)
      (at level 70, format "a  '⊑{' ϕ '}'  b", no associativity).

  Notation "a '≡{' ϕ '}' b" :=
    (behavior_equal ϕ a b)
      (at level 70, format "a  '≡{' ϕ '}'  b", no associativity).

  (* A definition of config refinement: *)
  (*    - if the target terminates on (v, m), *)
  (*    the source must either terminate on (v, m) or be stuck. *)
  (*    - if the target diverges, *)
  (*    the source must either diverges or be stuck. *)
  (*    - if the target is stuck, the source should also be stuck. *)
  Definition flex_refines ϕ (t: config Λt) (s: config Λs) : Prop :=
    ∀ b, b ∈ t -> ∃ b', b' ∈ s ∧ b ⊑{ϕ} b'.

  Definition rigid_refines ϕ (t: config Λt) (s: config Λs) : Prop :=
    ∀ b, b ∈ t -> ∃ b', b' ∈ s ∧ b ≡{ϕ} b'.
End Refinement.

Section SpecPreserving.
  Context {Λ: lang} (E: genv Λ).
  Instance beh_elem : ElemOf behavior (config Λ) := beh E.

  Definition Spec : Type := @behavior Λ -> Prop.
  Implicit Types (s : config Λ) (S : Spec).

  Definition meaningful S : Prop := ∀ b, S b -> b ≠ Undef.
  Definition match_spec s S : Prop :=  ∀ b, b ∈ s -> S b.
  Definition spec_preserved S s t : Prop := match_spec s S -> match_spec t S.

  Definition eq_rel (vt vs: value Λ) (mt ms: memory) : Prop := vt = vs ∧ mt = ms.

  Lemma refine_implies_meaningful_spec_preserve t s:
    flex_refines E E eq_rel t s -> ∀ S, meaningful S -> spec_preserved S s t.
  Proof using Type.
    intros Href S Hmean Hspec b Hb.
    apply Href in Hb as (b' & Hb & Hord).
    apply Hspec in Hb.
    destruct Hord as [ ? ? ? ? (-> & ->) | | ].
    - done.
    - done.
    - exfalso. by eapply Hmean.
  Qed.
End SpecPreserving.
