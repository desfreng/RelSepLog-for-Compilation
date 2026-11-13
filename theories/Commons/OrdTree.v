From RSL Require Import Prelude.

From RSL.Commons Require Import WfRel.

From Stdlib.Relations Require Import Relation_Operators.

From Stdlib Require Import Classical.
From Stdlib Require Import ClassicalChoice.

Section Def.
  Context (A: Type).

  Inductive ord_tree: Type :=
  | ord_tree_base
  | ord_tree_cons (childs: A -> ord_tree).

  Variant ord_tree_lt_ : relation ord_tree :=
  | ord_tree_lt_intro childs a : ord_tree_lt_ (childs a) (ord_tree_cons childs).

  Lemma ord_tree_lt__wf : well_founded ord_tree_lt_.
  Proof using Type.
    intro x.
    induction x as [| childs IH];
      constructor; intros y Hlt; now inv Hlt.
  Qed.

  Definition ord_tree_lt : relation ord_tree :=
    clos_trans ord_tree ord_tree_lt_.

  Lemma ord_tree_lt_wf : well_founded ord_tree_lt.
  Proof using Type.
    by apply Transitive_Closure.wf_clos_trans, ord_tree_lt__wf.
  Qed.

  Lemma ord_tree_lt_trans : Transitive ord_tree_lt.
  Proof using Type. by econstructor. Qed.

  Canonical Structure WfOrdTree : WfRel :=
    {|
      element := ord_tree;
      wf := ord_tree_lt_wf;
      trans := ord_tree_lt_trans
    |}.

  Lemma ord_tree_join (P: A -> Prop) (R: A -> ord_tree -> Prop)
    (ORD: ∀ a, P a -> ∃ o, R a o) :
    ∃ o, ∀ a, P a -> ∃ o', R a o' ∧ o' ⊏ o.
  Proof using Type.
    assert (Hchoice: ∀ a, ∃ o, P a -> R a o).
    { intro a. destruct (classic (P a)) as [H | H].
      - destruct (ORD a H) as [o Ho]. exists o. intro. exact Ho.
      - exists ord_tree_base. intro Hcontra. contradiction. }
    apply choice in Hchoice. destruct Hchoice as [f Hf].
    exists (ord_tree_cons f). intros a Ha.
    exists (f a). split.
    - now auto.
    - now constructor.
  Qed.
End Def.
