From RSL Require Import Prelude.

From Stdlib Require Import Classical.
From Stdlib Require Import ClassicalChoice.

Section Def.
  Context (A: Type).

  Inductive ord_tree: Type :=
  | ord_tree_base
  | ord_tree_cons (childs: A -> ord_tree).

  Variant ord_tree_lt: ord_tree -> ord_tree -> Prop :=
  | ord_tree_lt_intro childs a : ord_tree_lt (childs a) (ord_tree_cons childs).

  Lemma ord_tree_wf : well_founded ord_tree_lt.
  Proof using Type.
    intro x.
    induction x as [| childs IH];
      constructor; intros y Hlt; now inv Hlt.
  Qed.

  Program Canonical Structure WfOrdTree : WfRel :=
    {| element := ord_tree; lt := tc ord_tree_lt |}.
  Next Obligation.
    apply Inclusion.wf_incl with (Relation_Operators.clos_trans _ ord_tree_lt).
    - intros x y H. induction H as [ | ? ? ? H Ht IH ].
      + now constructor.
      + econstructor 2; try eassumption.
        now constructor.
    - apply Transitive_Closure.wf_clos_trans.
      apply ord_tree_wf.
  Qed.

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
