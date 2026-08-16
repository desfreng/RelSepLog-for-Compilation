From RSL Require Import Prelude.

From Stdlib Require Import Relations.Relation_Operators.

From Stdlib Require Import Wellfounded.Wellfounded.
From Stdlib Require Import Arith.Wf_nat.

Structure WfRel : Type :=
  wf_rel
    {
      element :> Type;
      lt : relation element;
      wf : well_founded lt;
      trans : Transitive lt;
    }.

Arguments lt {_} _ _.
Arguments wf {_} _.

Notation "x ⊏ y" := (lt x y) (at level 70).

Definition le {W: WfRel} : relation W := fun x y => x ⊏ y ∨ x = y.

Notation "x ⊑ y" := (le x y) (at level 70).

Global Instance WfRel_SqSubsetEq {W: WfRel} : SqSubsetEq W := le.

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

Lemma lt_from_le_lt {W:WfRel} (x y z : W) :
  x ⊑ y -> y ⊏ z -> x ⊏ z.
Proof. intros [Hxy| ->] Hyz; auto. now transitivity y. Qed.

Lemma lt_from_lt_le {W:WfRel} (x y z : W) :
  x ⊏ y -> y ⊑ z -> x ⊏ z.
Proof. intros Hxy [Hyz| ->]; auto. now transitivity y. Qed.

Class HasSucc {W: WfRel} (x: W) := {
    succ : W;
    is_succ: x ⊏ succ;
  }.

Arguments succ {W} x {_}.
Arguments is_succ {W} x {_}.

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

Section UnitWfRel.
  Definition unit_lt : relation unit := fun _ _ => False.

  Local Lemma unit_lt_wf : well_founded unit_lt.
  Proof.
    intros []; constructor; intros [] H; inv H.
  Qed.

  Local Lemma unit_lt_trans : Transitive unit_lt.
  Proof. intros x y z Hxy Hyz. inv Hxy. Qed.

  Canonical Structure WfUnit: WfRel :=
    {|
      wf := unit_lt_wf;
      trans := unit_lt_trans;
    |}.
End UnitWfRel.

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

Definition inter {A} (R1 R2: relation A) : relation A :=
  fun x y => R1 x y ∧ R2 x y.

Definition lift_rel {A B} (f: A -> B) (R: relation B) : relation A :=
  fun x y => R (f x) (f y).

Section ProdWfRel.
  Context (W X: WfRel).

  Definition prod_lt : relation (W * X) :=
    inter (lift_rel fst lt) (lift_rel snd lt).

  Local Lemma prod_lt_wf : well_founded prod_lt.
  Proof using Type.
    intros [w x]. revert x.
    induction w as [w IH] using (well_founded_induction wf).
    constructor. intros [w' x'] [Hw _].
    by apply IH, Hw.
  Qed.

  Local Lemma prod_lt_trans : Transitive prod_lt.
  Proof using Type.
    intros x y z [Hxy1 Hxy2] [Hyz1 Hyz2].
    split; unfold lift_rel in *; by etransitivity.
  Qed.

  Canonical Structure WfProd : WfRel :=
    {|
      wf := prod_lt_wf;
      trans := prod_lt_trans;
    |}.
End ProdWfRel.

Section LexProdWfRel.
  Context (W: WfRel) (X: WfRel).

  Variant ord_prod : Type := ord_pair (w: W) (x: X).

  Local Definition ord_prod_lt : relation ord_prod :=
    fun '(ord_pair w1 x1) '(ord_pair w2 x2) =>
      slexprod _ _ lt lt (w1, x1) (w2, x2).

  Local Definition pair_rel '(ord_pair x1 w1) '(x2, w2) :=
    x1 = x2 ∧ w1 = w2.

  Local Lemma ord_prod_wf : well_founded ord_prod_lt.
  Proof using Type.
    intros [].
    eapply Acc_simulation with (F := pair_rel) (b := (_, _)).
    - apply (wf_slexprod W X _ _ wf wf).
    - intros [x1 w1] [x2 w2] [x3 w3]. simpl.
      intros H [-> ->]. by eexists (_, _).
    - by split.
  Qed.

  Local Lemma ord_prod_trans : Transitive ord_prod_lt.
  Proof using Type.
    intros [? ?] [? ?] [? ?]. simpl.
    intros Hxy Hyz. inv Hxy; inv Hyz.
    - left. by etransitivity.
    - by left.
    - by left.
    - right. by etransitivity.
  Qed.

  Canonical Structure WfLexProd : WfRel :=
    {|
      wf := ord_prod_wf;
      trans := ord_prod_trans;
    |}.
End LexProdWfRel.

Section UnionWfRel.
  Context (W X: WfRel).

  Local Lemma le_AsB_trans : Transitive (le_AsB W X lt lt).
  Proof using Type.
    intros x y z Hxy Hyz.
    inv Hxy; inv Hyz; constructor; etransitivity; eassumption.
  Qed.

  Canonical Structure WfUnion : WfRel :=
    {|
      wf := wf_disjoint_sum _ _ _ _ wf wf;
      trans := le_AsB_trans;
    |}.
End UnionWfRel.
