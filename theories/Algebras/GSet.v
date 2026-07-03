From RSL Require Import Prelude.
From RSL.Algebras Require Import RA Updates LocalUpdates.

From stdpp Require Export sets gmap mapset.

(* The union RA *)
Section gset.
  Context `{Countable K}.
  Implicit Types X Y : gset K.

  Local Instance gset_valid_instance : Valid (gset K) := λ _, True.
  Local Instance gset_unit_instance : Unit (gset K) := (∅ : gset K).
  Local Instance gset_op_instance : Op (gset K) := union.
  Local Instance gset_pcore_instance : PCore (gset K) := λ X, Some X.

  Lemma gset_op X Y : X ⋅ Y = X ∪ Y.
  Proof using Type. done. Qed.

  Lemma gset_core X : core X = X.
  Proof using Type. done. Qed.

  Lemma gset_included X Y : X ≼ Y ↔ X ⊆ Y.
  Proof using Type.
    split.
    - intros [Z ->]. rewrite gset_op. set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L. by exists Z.
  Qed.

  Lemma gset_ra_mixin : RaMixin (gset K).
  Proof using Type.
    constructor; eauto.
    - set_solver.
    - set_solver.
    - intros x cx Heq. inv Heq. set_solver.
    - intros x y cx Hle Heq. inv Heq. now exists y.
  Qed.

  Canonical Structure gsetRA := Ra (gset K) gset_ra_mixin.

  Lemma gset_ura_mixin : URaMixin (gset K).
  Proof using Type.
    split; [ done | | done ].
    intros x. set_solver.
  Qed.

  Canonical Structure gsetURA := URa (gset K) gset_ura_mixin.

  Lemma gset_opM X mY : X ⋅? mY = X ∪ default ∅ mY.
  Proof using Type.
    destruct mY; simpl; set_solver.
  Qed.

  Lemma gset_update X Y : X ~~> Y.
  Proof using Type. done. Qed.

  Lemma gset_local_update X Y X' : X ⊆ X' → (X,Y) ~l~> (X',X').
  Proof using Type.
    intros (Z&->&?)%subseteq_disjoint_union_L.
    intros [Z'|]; simpl in *; subst.
    - split; [done|]. set_solver.
    - split; [done|]. set_solver.
  Qed.

  Global Instance gset_core_id X : CoreId X.
  Proof using Type. by apply core_id_total; rewrite gset_core. Qed.

  (* Lemma big_opS_singletons X : *)
  (*   ([^op set] x ∈ X, {[ x ]}) = X. *)
  (* Proof using Type. *)
  (*   induction X as [|x X Hx IH] using set_ind_L. *)
  (*   - rewrite big_opS_empty. done. *)
  (*   - unfold_leibniz. rewrite big_opS_insert // IH //. *)
  (* Qed. *)

  (** Add support [X ≼ Y] to [set_solver]. (We get support for [⋅] for free
  because it is definitionally equal to [∪]). *)
  Global Instance set_unfold_gset_included X Y Q :
    SetUnfold (X ⊆ Y) Q → SetUnfold (X ≼ Y) Q.
  Proof using Type. intros [?]; constructor. by rewrite gset_included. Qed.
End gset.

Global Arguments gsetRA _ {_ _}.
Global Arguments gsetURA _ {_ _}.

(* The disjoint union RA *)
Variant gset_disj K `{Countable K} :=
| GSet : gset K → gset_disj K
| GSetInvalid : gset_disj K.

Instance eq_dec_gset_disj `{Countable K} `{EqDecision K} : EqDecision (gset_disj K).
Proof. solve_decision. Qed.

Global Arguments GSet {_ _ _} _.
Global Arguments GSetInvalid {_ _ _}.

Section gset_disj.
  Context `{Countable K}.
  Local Arguments op _ _ !_ !_ /.
  Local Arguments ra_op _ !_ !_ /.
  Local Arguments ura_op _ !_ !_ /.

  Global Instance GSet_inj : Inj (=@{gset K}) (=) GSet.
  Proof using Type. intros ???. naive_solver. Qed.

  Local Instance gset_disj_valid_instance : Valid (gset_disj K) := λ X,
    match X with GSet _ => True | GSetInvalid => False end.
  Local Instance gset_disj_unit_instance : Unit (gset_disj K) := GSet ∅.
  Local Instance gset_disj_op_instance : Op (gset_disj K) := λ X Y,
    match X, Y with
    | GSet X, GSet Y => if decide (X ## Y) then GSet (X ∪ Y) else GSetInvalid
    | _, _ => GSetInvalid
    end.
  Local Instance gset_disj_pcore_instance : PCore (gset_disj K) := λ _, Some ε.

  Ltac gset_disj_solve :=
    repeat (simpl || case_decide);
    first [apply (f_equal GSet)|done|exfalso]; set_solver by eauto.

  Lemma gset_disj_included X Y : GSet X ≼ GSet Y ↔ X ⊆ Y.
  Proof using Type.
    split.
    - intros [[Z|] Heq]; inv Heq; simpl; try case_decide; set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L.
      exists (GSet Z). gset_disj_solve.
  Qed.

  Lemma gset_disj_valid_inv_l X Y : ✓ (GSet X ⋅ Y) → ∃ Y', Y = GSet Y' ∧ X ## Y'.
  Proof using Type. destruct Y; repeat (simpl || case_decide); by eauto. Qed.

  Lemma gset_disj_union X Y : X ## Y → GSet X ⋅ GSet Y = GSet (X ∪ Y).
  Proof using Type. intros. simpl. by rewrite decide_True. Qed.

  Lemma gset_disj_valid_op X Y : ✓ (GSet X ⋅ GSet Y) ↔ X ## Y.
  Proof using Type. simpl. case_decide; by split. Qed.

  Lemma gset_disj_ra_mixin : RaMixin (gset_disj K).
  Proof using Type.
    constructor; eauto.
    - intros [X1|] [X2|] [X3|]; gset_disj_solve.
    - intros [X1|] [X2|]; gset_disj_solve.
    - intros [|] cx Heq; inv Heq; auto. gset_disj_solve.
    - intros [X1|] [X2|] [X3|] Hlt Heq; inv Heq;
        exists (GSet ∅); split; try apply gset_disj_included; gset_disj_solve.
    - intros [X1|] [X2|]; gset_disj_solve.
  Qed.

  Canonical Structure gset_disjRA := Ra (gset_disj K) gset_disj_ra_mixin.

  Lemma gset_disj_ura_mixin : URaMixin (gset_disj K).
  Proof using Type. split; try apply _ || done. intros [X|]; gset_disj_solve. Qed.

  Canonical Structure gset_disjURA := URa (gset_disj K) gset_disj_ura_mixin.

  Lemma gset_disj_alloc_updateP_strong P (Q : gset_disj K → Prop) X :
    (∀ Y, X ⊆ Y → ∃ j, (j ∉ Y) ∧ P j) →
    (∀ i, i ∉ X → P i → Q (GSet ({[i]} ∪ X))) →
    GSet X ~~>: Q.
  Proof using Type.
    intros Hfresh HQ.
    apply ra_total_updateP. intros ? [Y [->?]]%gset_disj_valid_inv_l.
    destruct (Hfresh (X ∪ Y)) as (i&?&?); first set_solver.
    exists (GSet ({[ i ]} ∪ X)); split.
    - apply HQ; set_solver by eauto.
    - apply gset_disj_valid_op. set_solver by eauto.
  Qed.

  Lemma gset_disj_alloc_updateP_strong' P X :
    (∀ Y, X ⊆ Y → ∃ j, (j ∉ Y) ∧ P j) →
    GSet X ~~>: λ Y, ∃ i, Y = GSet ({[ i ]} ∪ X) ∧ (i ∉ X) ∧ P i.
  Proof using Type. eauto using gset_disj_alloc_updateP_strong. Qed.

  Lemma gset_disj_alloc_empty_updateP_strong P (Q : gset_disj K → Prop) :
    (∀ Y : gset K, ∃ j, (j ∉ Y) ∧ P j) →
    (∀ i, P i → Q (GSet {[i]})) → GSet ∅ ~~>: Q.
  Proof using Type.
    intros. apply (gset_disj_alloc_updateP_strong P); eauto.
    intros i; rewrite @ura_unit_r; auto.
  Qed.

  Lemma gset_disj_alloc_empty_updateP_strong' P :
    (∀ Y : gset K, ∃ j, (j ∉ Y) ∧ P j) →
    GSet ∅ ~~>: λ Y, ∃ i, Y = GSet {[ i ]} ∧ P i.
  Proof using Type. eauto using gset_disj_alloc_empty_updateP_strong. Qed.

  Section fresh_updates.
    Context `{!Infinite K}.

    Lemma gset_disj_alloc_updateP (Q : gset_disj K → Prop) X :
      (∀ i, i ∉ X → Q (GSet ({[i]} ∪ X))) → GSet X ~~>: Q.
    Proof using Type*.
      intro; eapply gset_disj_alloc_updateP_strong with (λ _, True); eauto.
      intros Y ?; exists (fresh Y). split; [|done]. apply is_fresh.
    Qed.

    Lemma gset_disj_alloc_updateP' X :
      GSet X ~~>: λ Y, ∃ i, Y = GSet ({[ i ]} ∪ X) ∧ i ∉ X.
    Proof using Type*. eauto using gset_disj_alloc_updateP. Qed.

    Lemma gset_disj_alloc_empty_updateP (Q : gset_disj K → Prop) :
      (∀ i, Q (GSet {[i]})) → GSet ∅ ~~>: Q.
    Proof using Type*.
      intro. apply gset_disj_alloc_updateP. intros i; rewrite @ura_unit_r; auto.
    Qed.

    Lemma gset_disj_alloc_empty_updateP' : GSet ∅ ~~>: λ Y, ∃ i, Y = GSet {[ i ]}.
    Proof using Type*. eauto using gset_disj_alloc_empty_updateP. Qed.
  End fresh_updates.

  Lemma gset_disj_dealloc_local_update X Y :
    (GSet X, GSet Y) ~l~> (GSet (X ∖ Y), GSet ∅).
  Proof using Type.
    apply local_update_total_valid. intros _ _ HYX%gset_disj_included.
    intros [[Xf|]|]; simpl.
    - intros _ Heq. destruct (decide _) as [HXf|]; inv Heq.
      assert (Hf: (Y ∪ Xf) ∖ Y = Xf) by set_solver.
      rewrite Hf. split; [easy|].
      rewrite decide_True; gset_disj_solve.
    - intros  _ Heq; inv Heq.
    - intros _ Heq. inv Heq. split.
      + easy.
      + gset_disj_solve.
  Qed.

  Lemma gset_disj_dealloc_empty_local_update X Z :
    (GSet Z ⋅ GSet X, GSet Z) ~l~> (GSet X, GSet ∅).
  Proof using Type.
    apply local_update_total_valid. intros HZX%gset_disj_valid_op _ _.
    assert (X = (Z ∪ X) ∖ Z) as HX by set_solver.
    rewrite gset_disj_union; auto.
    rewrite HX at 2. apply gset_disj_dealloc_local_update.
  Qed.

  Lemma gset_disj_dealloc_op_local_update X Y Z :
    (GSet Z ⋅ GSet X, GSet Z ⋅ GSet Y) ~l~> (GSet X, GSet Y).
  Proof using Type.
    rewrite <-(@ura_unit_l _ (GSet Y)) at 2.
    apply op_local_update_frame, gset_disj_dealloc_empty_local_update.
  Qed.

  Lemma gset_disj_alloc_op_local_update X Y Z :
    Z ## X → (GSet X,GSet Y) ~l~> (GSet Z ⋅ GSet X, GSet Z ⋅ GSet Y).
  Proof using Type.
    intros. apply op_local_update. by rewrite gset_disj_valid_op.
  Qed.

  Lemma gset_disj_alloc_local_update X Y Z :
    Z ## X → (GSet X,GSet Y) ~l~> (GSet (Z ∪ X), GSet (Z ∪ Y)).
  Proof using Type.
    intros. apply local_update_total_valid. intros _ _ ?%gset_disj_included.
    rewrite <-!gset_disj_union; auto; last set_solver.
    auto using gset_disj_alloc_op_local_update.
  Qed.

  Lemma gset_disj_alloc_empty_local_update X Z :
    Z ## X → (GSet X, GSet ∅) ~l~> (GSet (Z ∪ X), GSet Z).
  Proof using Type.
    intros. rewrite <-(@ura_unit_r _ Z) at 2.
    apply gset_disj_alloc_local_update; set_solver.
  Qed.

  (** Add some basic support for [GSet X = GSet Y], [GSet X ≼ GSet Y], and
  [✓ (GSet X ⋅ GSet Y)] to [set_solver]. There are probably more cases we could
  cover (e.g., involving [GSetInvalid], or nesting of [⋅]), but it is not clear
  these are useful in practice, nor how to handle them effectively. *)
  Global Instance set_unfold_gset_eq (X Y : gset K) Q :
    SetUnfold (X = Y) Q → SetUnfold (GSet X = GSet Y) Q.
  Proof using Type. intros [?]; constructor. by rewrite (inj_iff _). Qed.
  Global Instance set_unfold_gset_disj_included (X Y : gset K) Q :
    SetUnfold (X ⊆ Y) Q → SetUnfold (GSet X ≼ GSet Y) Q.
  Proof using Type. intros [?]; constructor. by rewrite gset_disj_included. Qed.
  Global Instance set_unfold_gset_disj_valid_op (X Y : gset K) Q :
    SetUnfold (X ## Y) Q → SetUnfold (✓ (GSet X ⋅ GSet Y)) Q.
  Proof using Type. intros [?]; constructor. by rewrite gset_disj_valid_op. Qed.
End gset_disj.

Global Arguments gset_disjRA _ {_ _}.
Global Arguments gset_disjURA _ {_ _}.
