From RSL Require Import Prelude.

From RSL.Commons Require Export Values.

From stdpp Require Import gmap.

Definition reg := nat.

(* [regmap] is a mapping from registers to a value *)
Definition regbank : Type := gmap reg val.

Implicit Type (ρ ρt ρs: regbank) (r: reg) (v: val) (rl: list reg) (vl: list val).

Definition regbank_get ρ r : val :=
  match ρ !! r with
  | Some v => v
  | None => VUndef
  end.

Definition regbank_set ρ r v : regbank := <[r := v]>ρ.

(** ** Logical Connectives  *)

Notation "'⟦' r '⇐' v '⟧' ρ" :=
  (regbank_set ρ r%nat v%Z)
    (at level 20, ρ at level 20, right associativity).

Class LogicRegisterAssert (R V : Type) :=
  regbank_assert : regbank -> R -> V -> Prop.

Instance regbank_assert_single : LogicRegisterAssert reg val :=
  fun ρ key val => regbank_get ρ key = val.

Instance regbank_assert_list : LogicRegisterAssert (list reg) (list val) :=
  fun ρ keys vals => map (regbank_get ρ) keys = vals.

Notation "ρ @ r '⇒' v" :=
  (regbank_assert ρ r%nat v%Z)
    (at level 60, no associativity).

Definition regbank_same I ρt ρs kt ks :=
  ∃ vt vs,
    ρt@kt ⇒ vt ∧
    ρs@ks ⇒ vs ∧
    same_val I vt vs.

Notation "ρt @ rt '<{' I '}>' ρs @ rs" :=
  (regbank_same I ρt ρs rt rs)
    (at level 60, ρs at next level, no associativity).

Create HintDb regbank discriminated.

Hint Unfold
  regbank
  regbank_get
  regbank_set
  regbank_assert
  regbank_assert_single
  regbank_assert_list
  regbank_same : regbank.

Lemma regbank_assert_fold ρ :
  ∀ r v rl vl,
  ρ @ r ⇒ v ->
  ρ @ rl ⇒ vl ->
  ρ @ (r :: rl) ⇒ (v :: vl).
Proof.
  autounfold with regbank.
  intros r v tl vl Hv Htl.
  simpl. now f_equal.
Qed.

Lemma regbank_assert_unfold ρ :
  ∀ r v rl vl,
  ρ @ (r :: rl) ⇒ (v :: vl) ->
  ρ @ r ⇒ v ∧ ρ @ rl ⇒ vl.
Proof.
  autounfold with regbank.
  intros r v rl vl H.
  by inv H.
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
  ∀ r, ∃ v, ρ @ r ⇒ v.
Proof. intros r. by eexists. Qed.

Lemma regbank_never_empty_list ρ:
  ∀ rl, ∃ vl, ρ @ rl ⇒ vl.
Proof. intros r. by eexists. Qed.

Lemma regbank_simpl_inj ρ:
  ∀ r v1 v2,
  ρ @ r ⇒ v1 ->
  ρ @ r ⇒ v2 ->
  v1 = v2.
Proof.
  autounfold with regbank in *.
  intros r v1 v2 <- ->.
  easy.
Qed.

Lemma regbank_list_inj ρ:
  ∀ rl (v1 v2 : list val),
  ρ @ rl ⇒ v1 ->
  ρ @ rl ⇒ v2 ->
  v1 = v2.
Proof.
  autounfold with regbank in *.
  intros r v1 v2 <- ->.
  easy.
Qed.

Lemma regbank_list_length ρ:
  ∀ rl vl,
  ρ @ rl ⇒ vl ->
  length vl = length rl.
Proof.
  autounfold with regbank in *.
  intros rl vl <-.
  now apply length_map.
Qed.

Definition init_regs rl vl : regbank := list_to_map (zip rl vl).

Lemma init_regs_sound regs vals :
  NoDup regs ->
  ∃ ρ,
    ρ = init_regs regs vals ∧
    ∀ i r v,
      regs !! i = Some r ->
      vals !! i = Some v ->
      ρ@r ⇒ v.
Proof using Type.
  intros HnoDup.
  eexists. split; [ done | ].
  intros i r v Hr Hv.
  autounfold with regbank.
  unfold init_regs, regbank.
  rewrite (elem_of_list_to_map_1' _ r v); auto.
  - intros y (i' & ? & ? & Heq & Hr' & Hv')%elem_of_lookup_zip_with.
    inv Heq.
    assert (i = i').
    + by eapply NoDup_lookup.
    + congruence.
  - apply elem_of_lookup_zip_with. by exists i, r, v.
Qed.

Lemma init_same_bank I regs valt vals :
  Forall2 (same_val I) valt vals ->
  ∀ r, init_regs regs valt @ r <{ I }> init_regs regs vals @ r.
Proof using Type.
  autounfold with regbank in *.
  unfold init_regs, regbank.
  revert valt vals.
  induction regs as [ | reg regs IH].
  {
    intros valt vals H r. simpl.
    exists VUndef, VUndef.
    split_and!.
    - by rewrite lookup_empty.
    - by rewrite lookup_empty.
    - by constructor.
  }
  intros valt vals H r.
  destruct valt as [|vt valt].
  - inv H. simpl.
    exists VUndef, VUndef.
    split_and!.
    + by rewrite lookup_empty.
    + by rewrite lookup_empty.
    + by constructor.
  - inv H as [ | ? vs ? vals' Hrel Hforall ]. simpl.
    destruct (decide (r = reg)) as [-> | Hneq].
    + eexists vt, vs.
      split_and!.
      * by rewrite lookup_insert_eq.
      * by rewrite lookup_insert_eq.
      * done.
    + destruct (IH _ _ Hforall r) as (vt' & vs' & ? & ? & Hrel').
      eexists vt', vs'. split_and!.
      * by rewrite lookup_insert_ne.
      * by rewrite lookup_insert_ne.
      * done.
Qed.

Lemma update_same_bank I ρt ρs dst vt vs:
  same_val I vt vs ->
  (∀ r, r ≠ dst -> ρt @ r <{ I }> ρs @ r) ->
  ∀ r, ⟦ dst ⇐ vt ⟧ ρt @ r <{ I }> ⟦ dst ⇐ vs ⟧ ρs @ r.
Proof using Type.
  intros Hrel Hsame r.
  destruct (decide (r = dst)) as [-> | HnEq].
  - exists vt, vs. split_and!.
    + by apply regbank_set_use.
    + by apply regbank_set_use.
    + done.
  - destruct (Hsame _ HnEq) as (vt' & vs' & Ht & Hs & Hrel').
    exists vt', vs'. split_and!.
    + by apply regbank_set_discard.
    + by apply regbank_set_discard.
    + done.
Qed.

Lemma same_bank_mono I I' ρt ρs:
  I ⊆ I' ->
  (∀ r, ρt @ r <{ I }> ρs @ r) ->
  ∀ r, ρt @ r <{ I' }> ρs @ r.
Proof using Type.
  intros Hincl Hsame r.
  destruct (Hsame r) as (vt & vs & Ht & Hs & Hrel).
  exists vt, vs. split_and!.
  - done.
  - done.
  - by eapply same_val_mono.
Qed.

Lemma multiple_same {I ρt ρs} args:
  (∀ r, ρt @ r <{ I }> ρs @ r) ->
  ∃ vt vs,
    ρt @ args ⇒ vt ∧
    ρs @ args ⇒ vs ∧
    Forall2 (same_val I) vt vs.
Proof using Type.
  intros Hsame.
  induction args as [ | hd tl (vlt & vls & Hlt & Hls & Hl)].
  - exists [], []. split_and!.
    + by apply regbank_assert_nil.
    + by apply regbank_assert_nil.
    + by constructor.
  - destruct (Hsame hd) as (vt & vs & Ht & Hs & H).
    exists (vt :: vlt), (vs :: vls). split_and!.
    + by apply regbank_assert_fold.
    + by apply regbank_assert_fold.
    + by constructor.
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
      apply regbank_assert_fold; simpl_regs tac
  | [ H1: ?ρ @ ?r ⇒ ?v1, H2: ?ρ @ ?r ⇒ ?v2 |- _ ] =>
      let Heq := fresh "Heq" in
      assert (Heq: v2 = v1) by
        (apply (regbank_simpl_inj _ _ _ _ H2 H1)
         || apply (regbank_list_inj _ _ _ _ H2 H1));
      simplify_eq;
      clear H2; try (simpl_regs tac)
  end.

Global Tactic Notation "simregs" := simpl_regs lia.
