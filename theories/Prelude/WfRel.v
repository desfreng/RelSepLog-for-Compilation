From stdpp Require Import prelude.

From Stdlib Require Import Relation_Operators.

From Stdlib Require Import Wellfounded.Wellfounded.
From Stdlib Require Import Arith.Wf_nat.

Structure WfRel : Type :=
  wf_rel
    {
      element: Type;
      lt: relation element;
      wf: well_founded lt;
      trans: Transitive lt;
    }.

Coercion element : WfRel >-> Sortclass.

Arguments lt {_} _ _.
Arguments wf {_} _.

Notation "x ⊏ y" := (lt x y) (at level 70).

Definition le {W: WfRel} : relation W := fun x y => x ⊏ y ∨ x = y.

Notation "x ⊑ y" := (le x y) (at level 70).

Global Instance lt_trans {W: WfRel} : Transitive (@lt W).
Proof. apply trans. Qed.

Global Instance lt_irrel {W: WfRel} : Irreflexive (@lt W).
Proof.
  intros x H.
  induction x as [x IH] using (well_founded_induction wf).
  now apply IH with x.
Qed.

Global Instance lt_strict_order {W: WfRel} : StrictOrder (@lt W)
  := Build_StrictOrder _ _ _.

Global Instance le_refl {W: WfRel} : Reflexive (@le W).
Proof. now constructor. Qed.

Global Instance le_trans {W: WfRel} : Transitive (@le W).
Proof.
  intros x y z Hxy Hyz. inv Hxy; inv Hyz; try now constructor.
  constructor; now transitivity y.
Qed.

Global Instance le_pre_order {W: WfRel} : PreOrder (@le W)
  := Build_PreOrder _ _ _.

Class NoIsolatedElements (W: WfRel) := {
  no_isolated : ∀ x : W, ∃ y, x ⊏ y ∨ y ⊏ x
  }.

Canonical Structure WfNat: WfRel := {| wf := lt_wf |}.

Global Instance nat_not_isolated : NoIsolatedElements WfNat.
Proof.
  constructor. intros x. exists (S x). left. simpl. lia.
Qed.

Section BoolWfRel.
  Variant bool_lt: relation bool :=
  | BoolLt : bool_lt false true.

  Local Lemma bool_lt_wf : well_founded bool_lt.
  Proof.
    intros []; constructor; intros [] H; inv H.
    constructor; intros [] H; inv H.
  Qed.

  Local Lemma bool_lt_trans : Transitive bool_lt.
  Proof. intros x y z Hxy Hyz. inv Hxy. inv Hyz. Qed.

  Canonical Structure WfBool: WfRel :=
    {|
      wf := bool_lt_wf;
      trans := bool_lt_trans;
    |}.

  Global Instance bool_not_isolated : NoIsolatedElements WfBool.
  Proof.
    constructor; intros []; eexists; (left; now constructor) || (right; now constructor).
  Qed.
End BoolWfRel.

Section WithTopWfRel.
  Context (W: WfRel).
 
  Variant lt_top : relation (option W) :=
  | LtTopSomeSome : ∀ x y, x ⊏ y -> lt_top (Some x) (Some y)
  | LtTopSomeNone : ∀ x, lt_top (Some x) None.

  Local Lemma lt_top_wf : well_founded lt_top.
  Proof using Type.
    assert (H: ∀ e, Acc lt_top (Some e)).
    { intros e.
      induction e as [e IH] using (well_founded_induction wf).
      constructor.
      intros [] Hlt; inv Hlt.
      now apply IH.
    }
    intros [].
    - apply H.
    - constructor. intros [] Hlt; inv Hlt.
      apply H.
  Qed.

  Local Lemma lt_top_trans : Transitive lt_top.
  Proof using Type.
    intros x y z Hxy Hyz. inv Hxy; inv Hyz; constructor.
    etransitivity; eassumption.
  Qed.

  Definition WfWithTop : WfRel :=
    {|
      wf := lt_top_wf;
      trans := lt_top_trans;
    |}.
End WithTopWfRel.

Section WithBotWfRel.
  Context (W: WfRel).

  Variant lt_bot : relation (option W) :=
  | LtBotSomeSome : ∀ x y, x ⊏ y -> lt_bot (Some x) (Some y)
  | LtBotNoneSome : ∀ x, lt_bot None (Some x).

  Local Lemma lt_bot_wf : well_founded lt_bot.
  Proof using Type.
    intros [e |].
    - induction e as [e IH] using (well_founded_induction wf).
      constructor.
      intros [] Hlt; inv Hlt.
      + now apply IH.
      + constructor. intros [] H; inv H.
    - constructor. intros [] Hlt; inv Hlt.
  Qed.

  Local Lemma lt_bot_trans : Transitive lt_bot.
  Proof using Type.
    intros x y z Hxy Hyz. inv Hxy; inv Hyz; constructor.
    etransitivity; eassumption.
  Qed.

  Definition WfWithBot : WfRel :=
    {|
      wf := lt_bot_wf;
      trans := lt_bot_trans;
    |}.
End WithBotWfRel.

Section LexProdWfRel.
  Context (W1 W2: WfRel).

  Local Lemma slexprod_trans : Transitive (slexprod W1 W2 lt lt).
  Proof using Type.
    intros x y z Hxy Hyz.
    inv Hxy; inv Hyz.
    - left. etransitivity; eassumption.
    - left. eassumption.
    - left. eassumption.
    - right. etransitivity; eassumption.
  Qed.

  Canonical Structure WfLexProd : WfRel :=
    {|
      wf := wf_slexprod W1 W2 _ _ wf wf;
      trans := slexprod_trans;
    |}.
End LexProdWfRel.

Section UnionWfRel.
  Context (W1 W2: WfRel).

  Local Lemma le_AsB_trans : Transitive (le_AsB W1 W2 lt lt).
  Proof using Type.
    intros x y z Hxy Hyz.
    inv Hxy; inv Hyz; constructor; etransitivity; eassumption.
  Qed.

  Canonical Structure WfUnion : WfRel :=
    {|
      wf := wf_disjoint_sum W1 W2 _ _ wf wf;
      trans := le_AsB_trans;
    |}.
End UnionWfRel.
