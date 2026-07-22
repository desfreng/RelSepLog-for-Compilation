From RSL Require Import Prelude.

From RSL.Commons Require Export Values.

From stdpp Require Import gmap.

Definition reg := nat.

(* [regmap] is a mapping from registers to a value *)
Definition regbank : Type := gmap reg val.

Definition regbank_get (ρ: regbank) (r: reg) : val :=
  match ρ !! r with
  | Some v => v
  | None => VUndef
  end.

Definition regbank_set (ρ: regbank) (r: reg) (v: val) : regbank :=
  <[r := v]>ρ.

(** ** Logical Connectives  *)

Class LogicRegisterAssert (R V : Type) :=
  regbank_assert : regbank -> R -> V -> Prop.

Instance regbank_assert_single : LogicRegisterAssert reg val :=
  fun ρ key val => regbank_get ρ key = val.

Instance regbank_assert_list : LogicRegisterAssert (list reg) (list val) :=
  fun ρ keys vals => map (regbank_get ρ) keys = vals.

Notation "ρ @ r '⇒' v" :=
  (regbank_assert ρ r%nat v%Z)
    (at level 60, no associativity).

Notation "'⟦' r '⇐' v '⟧' ρ" :=
  (regbank_set ρ r%nat v%Z)
    (at level 20, ρ at level 20, right associativity).

Create HintDb regbank discriminated.

Hint Unfold
  regbank
  regbank_get
  regbank_set
  regbank_assert
  regbank_assert_single
  regbank_assert_list : regbank.

Lemma regbank_assert_unfold ρ :
  ∀ r v tl tv,
  ρ @ r ⇒ v ->
  ρ @ tl ⇒ tv ->
  ρ @ (r :: tl) ⇒ (v :: tv).
Proof.
  autounfold with regbank.
  intros r v tl tv Hv Htl.
  simpl. now f_equal.
Qed.

Lemma regbank_assert_nil ρ :
  ρ @ [] ⇒ [].
Proof. now autounfold with regbank. Qed.

Lemma regbank_set_discard ρ :
  ∀ (r1 r2 : reg) v1 v2,
  r2 ≠ r1 ->
  ρ @ r1 ⇒ v1 ->
  ⟦r2 ⇐ v2⟧ρ @ r1 ⇒ v1.
Proof.
  autounfold with regbank.
  intros r1 r2 v1 v2 Hneq Hr.
  now rewrite lookup_insert_ne.
Qed.

Lemma regbank_set_discard_list :
  ∀ regs args r ρ v,
  r ∉ regs ->
  ρ @ regs ⇒ args ->
  ⟦r ⇐ v⟧ρ @ regs ⇒ args.
Proof using Type.
  autounfold with regbank.
  intros regs args r ρ v Hr Hmap.
  induction args as [| a args IH ] in regs, Hmap, Hr |- *.
  - apply map_eq_nil in Hmap. now subst regs.
  - apply map_eq_cons in Hmap.
    destruct Hmap as (reg & tl & -> & Hreg & Hmap).
    apply not_elem_of_cons in Hr.
    destruct Hr as [Hr Htl].
    simpl. f_equal.
    + now rewrite (lookup_insert_ne ρ).
    + now apply IH.
Qed.

Lemma regbank_set_use ρ :
  ∀ r v,
  ⟦r ⇐ v⟧ρ @ r ⇒ v.
Proof.
  autounfold with regbank.
  intros r v.
  now rewrite lookup_insert_eq.
Qed.

Lemma regbank_never_empty ρ:
  ∀ r : reg,
  ∃ v, ρ @ r ⇒ v.
Proof.
  autounfold with regbank.
  intros r.
  destruct (ρ !! r); now eexists.
Qed.

Lemma regbank_simpl_inj ρ:
  ∀ (r: reg) v1 v2,
  ρ @ r ⇒ v1 ->
  ρ @ r ⇒ v2 ->
  v1 = v2.
Proof.
  autounfold with regbank in *.
  intros r v1 v2 <- ->.
  easy.
Qed.

Lemma regbank_list_inj ρ:
  ∀ (r: list reg) v1 v2,
  ρ @ r ⇒ v1 ->
  ρ @ r ⇒ v2 ->
  v1 = v2.
Proof.
  autounfold with regbank in *.
  intros r v1 v2 <- ->.
  easy.
Qed.

Lemma regbank_list_length ρ:
  ∀ (regs: list reg) vals,
  ρ @ regs ⇒ vals ->
  length vals = length regs.
Proof.
  autounfold with regbank in *.
  intros regs vals <-.
  now apply length_map.
Qed.

Ltac simpl_regs tac :=
  match goal with
  | [ |- ?ρ @ [] ⇒ _ ] =>
      apply regbank_assert_nil
  | [ H: ?ρ @ ?r ⇒ ?v |- ?ρ @ ?r ⇒ _ ] =>
      exact H
  | [ |- ⟦?r ⇐ _⟧?ρ @ ?r ⇒ _ ] =>
      apply regbank_set_use
  | [ |- ⟦_ ⇐ _⟧?ρ @ ?r ⇒ _ ] =>
      apply regbank_set_discard; [tac| simpl_regs tac]
  | [ |- ?ρ @ (?r :: ?tl) ⇒ _ ] =>
      apply regbank_assert_unfold; simpl_regs tac
  | [ H1: ?ρ @ ?r ⇒ ?v1, H2: ?ρ @ ?r ⇒ ?v2 |- _ ] =>
      let Heq := fresh "Heq" in
      assert (Heq: v2 = v1) by
        (apply (regbank_simpl_inj _ _ _ _ H2 H1)
         || apply (regbank_list_inj _ _ _ _ H2 H1));
      simplify_eq;
      clear H2; try (simpl_regs tac)
  end.

Global Tactic Notation "simregs" := simpl_regs lia.
