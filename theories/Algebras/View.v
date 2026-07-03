From RSL Require Import Prelude.
From RSL Require Export Algebras.RA.
From RSL Require Export Algebras.BaseRA.
From RSL Require Export Algebras.Agree.
From RSL Require Export Algebras.DFrac.
From RSL Require Export Algebras.Mapping.
From RSL Require Export Algebras.Updates.
From RSL Require Export Algebras.LocalUpdates.

(* From iris.algebra Require Export updates local_updates frac dfrac agree. *)
(* From iris.algebra Require Import proofmode_classes big_op. *)
(* From iris.prelude Require Import options. *)

(** The view camera with fractional authoritative elements *)
(** The view camera, which is reminiscent of the views framework, is used to
  provide a logical/"small-footprint" "view" of some "large-footprint" piece of
  data, which can be shared in the separation logic sense, i.e., different parts
  of the data can be separately owned by different functions or threads. This is
  achieved using the two elements of the view camera:

- The authoritative element [●V a], which describes the data under consideration.
- The fragment [◯V b], which provides a logical view of the data [a].

To enable sharing of the fragments, the type of fragments is equipped with a
camera structure so ownership of fragments can be split. Concretely, fragments
enjoy the rule [◯V (b1 ⋅ b2) = ◯V b1 ⋅ ◯V b2].

To enable sharing of the authoritative element [●V{dq} a], it is equipped with a
discardable fraction [dq]. Updates are only possible with the full authoritative
element [●V a] (syntax for [●V{#1} a]]), while fractional authoritative elements
have agreement, i.e., [✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) → a1 = a2]. *)

(** * The view relation *)
(** To relate the authoritative element [a] to its possible fragments [b], the
view camera is parametrized by a (step-indexed) relation [view_rel n a b]. This
relation should be a.) closed under smaller step-indexes [n], b.) non-expansive
w.r.t. the argument [a], c.) closed under smaller [b] (which implies
non-expansiveness w.r.t. [b]), and d.) ensure validity of the argument [b].

Note 1: Instead of requiring both a step-indexed and a non-step-indexed version
of the relation (like cameras do for validity), we use [∀ n, view_rel n] as the
non-step-indexed version. This is anyway necessary when using [≼{n}] as the
relation (like the authoritative camera does) as its non-step-indexed version
is not equivalent to [∀ n, x ≼{n} y].

Note 2: The view relation is defined as a canonical structure so that given a
relation [nat → A → B → Prop], the instance with the laws can be inferred. We do
not use type classes for this purpose because cameras themselves are represented
using canonical structures. It has proven fragile for a canonical structure
instance to take a type class as a parameter (in this case, [viewR] would need
to take a class with the view relation laws). *)

Structure view_rel (A: Type) (B: ura) :=
  ViewRel
    {
      view_rel_holds :> A -> B -> Prop;
      view_rel_mono a b1 b2 :
        view_rel_holds a b1 ->
        b2 ≼ b1 ->
        view_rel_holds a b2;
      view_rel_valid a b : view_rel_holds a b → ✓ b;
      view_rel_unit : ∃ a, view_rel_holds a ε
    }.

(** * Definition of the view camera *)
(** To make use of the lemmas provided in this file, elements of [view] should
always be constructed using [●V] and [◯V], and never using the constructor
[View]. *)

Record view {A B} (rel : A -> B -> Prop) :=
  View { view_auth_proj : option (dfrac * agree A) ; view_frag_proj : B }.

Arguments View {_ _ _} _.
Arguments view_auth_proj {_ _ _} _.
Arguments view_frag_proj {_ _ _} _.

Instance vieq_eq_dec `{EqDecision A} `{EqDecision B} :
  ∀ rel : A -> B -> Prop, EqDecision (view rel).
Proof. solve_decision. Qed.

Definition view_auth {A B} {rel : view_rel A B} (dq : dfrac) (a : A) : view rel :=
  View (Some (dq, Ag a)) ε.

Definition view_frag {A B} {rel : view_rel A B} (b : B) : view rel :=
  View None b.

Notation "●V dq a" := (view_auth dq a)
  (at level 20, dq custom dfrac at level 1, format "●V dq  a").

Notation "◯V a" := (view_frag a) (at level 20).

Global Typeclasses Opaque view_auth view_frag.

(** * The ressource algebra structure *)
Section ra.
  Context A B (rel : view_rel A B) `{EqDecision A}.
  Implicit Types a : A.
  Implicit Types ag : option (dfrac * agree A).
  Implicit Types b : B.
  Implicit Types x y : view rel.

  Local Lemma view_eq x y :
    x = y <-> view_auth_proj x = view_auth_proj y ∧ view_frag_proj x = view_frag_proj y.
  Proof using Type.
    split.
    - by intros ->.
    - destruct x, y. simpl. intros []. congruence.
  Qed.

  Global Instance view_auth_inj : Inj2 (=) (=) (=) (@view_auth A B rel).
  Proof using Type.
    intros dq1 a1 dq2 a2 H. now inv H.
  Qed.

  Global Instance view_frag_inj : Inj (=) (=) (@view_frag A B rel).
  Proof using Type. by intros a a' [Hag ?]%view_eq. Qed.

  Local Instance view_valid_instance : Valid (view rel) := λ x,
    match view_auth_proj x with
    | Some (dq, ag) =>
       ✓ dq ∧ (∃ a, ag = Ag a ∧ rel a (view_frag_proj x))
    | None => ∃ a, rel a (view_frag_proj x)
  end.

  Local Instance view_pcore_instance : PCore (view rel) := λ x,
    Some (View (core (view_auth_proj x)) (core (view_frag_proj x))).

  Local Instance view_op_instance : Op (view rel) := λ x y,
    View (view_auth_proj x ⋅ view_auth_proj y) (view_frag_proj x ⋅ view_frag_proj y).

  Local Instance view_empty_instance : Unit (view rel) := View ε ε.

  Local Definition view_valid_eq :
    valid =
    fun x =>
      match view_auth_proj x with
      | Some (dq, ag) =>
          ✓ dq ∧ (∃ a, ag = Ag a ∧ rel a (view_frag_proj x))
      | None => ∃ a, rel a (view_frag_proj x)
      end := eq_refl _.

  Local Definition view_pcore_eq :
      pcore = λ x, Some (View (core (view_auth_proj x)) (core (view_frag_proj x))) :=
    eq_refl _.

  Local Definition view_core_eq :
      core = λ x, View (core (view_auth_proj x)) (core (view_frag_proj x)) :=
    eq_refl _.

  Local Definition view_op_eq :
      op = λ x y, View (view_auth_proj x ⋅ view_auth_proj y)
                       (view_frag_proj x ⋅ view_frag_proj y) :=
    eq_refl _.

  Lemma view_ra_mixin : RaMixin (view rel).
  Proof using Type.
    apply (iso_ra_mixin_restrict_validity
             (λ x : option (dfrac * agree A) * B, View x.1 x.2)
             (λ x, (view_auth_proj x, view_frag_proj x))).
    - intros [] []; simpl; rewrite view_eq; simpl in *. split.
      + by intros [-> ->].
      + intro H. by inv H.
    - simpl. by intros [].
    - intros [[ag|] b]; simpl;
        unfold pcore at 1; unfold prod_pcore_instance; simpl;
        by rewrite ra_pcore_core.
    - intros y1 y2. simpl. by unfold op, prod_op_instance.
    - rewrite view_valid_eq.
      intros [[[q ag]|] b] [a H].
      + destruct H as (? & Hag & Hrel). constructor; simpl;
          subst; by eauto using view_rel_valid.
      + constructor; simpl; by eauto using view_rel_valid.
    - unfold valid, view_valid_instance.
      intros [[[q1 ag1]|] b1] [[[q2 ag2]|] b2]; simpl in *.
      + intros (Hq & ag & [-> ->]%Ag_op_eq_inv' & Hrel).
        split; eauto using ra_valid_op_l, view_rel_mono, ra_included_l.
      + intros (Hq & ag & -> & Hrel).
        split; eauto using view_rel_mono, ra_included_l.
      + intros (Hq & ag & -> & Hrel).
        eauto using view_rel_mono, ra_included_l.
      + intros (ag & Hrel).
        eauto using view_rel_mono, ra_included_l.
  Qed.

  Canonical Structure viewRA := Ra (view rel) view_ra_mixin.

  Lemma view_ura_mixin : URaMixin (view rel).
  Proof using Type.
    constructor.
    - unfold valid, view_valid_instance. apply view_rel_unit.
    - intros [a b]. rewrite view_op_eq. f_equal.
      + simpl. apply (ura_unit_l a).
      + simpl. apply (ura_unit_l b).
    - rewrite view_pcore_eq. f_equal; simpl.
      by rewrite !(core_id_core _).
  Qed.

  Canonical Structure viewURA := URa (view rel) view_ura_mixin.

  Lemma view_auth_dfrac_op dq1 dq2 a : ●V{dq1 ⋅ dq2} a = ●V{dq1} a ⋅ ●V{dq2} a.
  Proof using Type.
    apply view_eq.
    split; simpl; last by rewrite @ura_unit_l.
    rewrite <-Some_op.
    f_equal.
    unfold op; simpl. unfold prod_op_instance. simpl.
    f_equal. symmetry.
    apply agree_idemp.
  Qed.

  Global Instance view_auth_dfrac_is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 → IsOp' (●V{dq} a) (●V{dq1} a) (●V{dq2} a).
  Proof using Type. unfold IsOp', IsOp. intros ->. by rewrite <-view_auth_dfrac_op. Qed.

  Lemma view_frag_op b1 b2 : ◯V (b1 ⋅ b2) = ◯V b1 ⋅ ◯V b2.
  Proof using Type. done. Qed.

  Lemma view_frag_mono b1 b2 : b1 ≼ b2 → ◯V b1 ≼ ◯V b2.
  Proof using Type.
    intros [c ->]. rewrite view_frag_op.
    now eexists.
  Qed.

  Lemma view_frag_core b : core (◯V b) = ◯V (core b).
  Proof using Type. done. Qed.

  Lemma view_both_core_discarded a b :
    core (●V□ a ⋅ ◯V b) = ●V□ a ⋅ ◯V (core b).
  Proof using Type.
    rewrite view_core_eq, view_op_eq. apply view_eq; split; simpl; auto.
    now rewrite !@ura_unit_l.
  Qed.

  Lemma view_both_core_frac q a b :
    core (●V{#q} a ⋅ ◯V b) = ◯V (core b).
  Proof using Type.
    rewrite view_core_eq, view_op_eq. apply view_eq; split; simpl; auto.
    now rewrite !@ura_unit_l.
  Qed.

  Global Instance view_auth_core_id a : CoreId (●V□ a).
  Proof using Type.
    unfold CoreId, view_auth, pcore. simpl.
    unfold view_pcore_instance. simpl.
    repeat f_equal.
    apply core_id_core.
    apply ura_unit_core_id.
  Qed.

  Global Instance view_frag_core_id b : CoreId b → CoreId (◯V b).
  Proof using Type.
    intros H.
    unfold CoreId, view_auth, pcore. simpl.
    unfold view_pcore_instance. simpl.
    repeat f_equal.
    by apply core_id_core.
  Qed.

  Global Instance view_both_core_id a b : CoreId b → CoreId (●V□ a ⋅ ◯V b).
  Proof using Type.
    intros H.
    unfold CoreId, op, view_auth, pcore, view_op_instance. simpl.
    unfold view_pcore_instance. simpl.
    repeat f_equal.
    rewrite !(@ura_unit_l B). by apply core_id_core.
  Qed.

  Global Instance view_frag_is_op b b1 b2 :
    IsOp b b1 b2 → IsOp' (◯V b) (◯V b1) (◯V b2).
  Proof using Type. intros ->. now rewrite view_frag_op. Qed.

  (* Lemma big_opL_view_frag {C} (g : nat → C → B) (l : list C) : *)
  (*   (◯V [^op list] k↦x ∈ l, g k x) = [^op list] k↦x ∈ l, ◯V (g k x). *)
  (* Proof using Type. apply (big_opL_commute _). Qed. *)
  (* Lemma big_opM_view_frag `{Countable K} {C} (g : K → C → B) (m : gmap K C) : *)
  (*   (◯V [^op map] k↦x ∈ m, g k x) = [^op map] k↦x ∈ m, ◯V (g k x). *)
  (* Proof using Type. apply (big_opM_commute _). Qed. *)
  (* Lemma big_opS_view_frag `{Countable C} (g : C → B) (X : gset C) : *)
  (*   (◯V [^op set] x ∈ X, g x) = [^op set] x ∈ X, ◯V (g x). *)
  (* Proof using Type. apply (big_opS_commute _). Qed. *)
  (* Lemma big_opMS_view_frag `{Countable C} (g : C → B) (X : gmultiset C) : *)
  (*   (◯V [^op mset] x ∈ X, g x) = [^op mset] x ∈ X, ◯V (g x). *)
  (* Proof using Type. apply (big_opMS_commute _). Qed. *)

  Lemma view_auth_dfrac_op_inv dq1 a1 dq2 a2 :
    ✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) → a1 = a2.
  Proof using Type.
    unfold op, view_op_instance. simpl.
    intros (?&?& Eq &?).
    eapply Ag_op_inv. simpl in Eq. now rewrite Eq.
  Qed.

  Lemma view_auth_dfrac_valid dq a :
    ✓ (●V{dq} a) ↔ ✓ dq ∧ rel a ε.
  Proof using Type.
    split.
    - intros (Hq & ag & Hag & Hrel). split; auto.
      inv Hag. apply Hrel.
    - intros [Hq Hrel]. split; auto.
      exists a. now split.
  Qed.

  Lemma view_auth_valid a : ✓ (●V a) ↔ rel a ε.
  Proof using Type.
    rewrite view_auth_dfrac_valid. split; [naive_solver|done].
  Qed.

  Lemma view_auth_dfrac_op_valid dq1 dq2 a1 a2 :
    ✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) ↔ ✓(dq1 ⋅ dq2) ∧ a1 = a2 ∧ rel a1 ε.
  Proof using Type.
    split.
    - intros Hval. assert (a1 = a2) as Ha by eauto using view_auth_dfrac_op_inv.
      revert Hval. rewrite Ha, <-view_auth_dfrac_op, view_auth_dfrac_valid. naive_solver.
    - intros (?&->&?). by rewrite <-view_auth_dfrac_op, view_auth_dfrac_valid.
  Qed.

  Lemma view_auth_op_valid a1 a2 : ✓ (●V a1 ⋅ ●V a2) ↔ False.
  Proof using Type. rewrite view_auth_dfrac_op_valid. naive_solver. Qed.

  Lemma view_frag_valid b : ✓ (◯V b) ↔ ∃ a, rel a b.
  Proof using Type. done. Qed.

  Lemma view_both_dfrac_valid dq a b :
    ✓ (●V{dq} a ⋅ ◯V b) ↔ ✓dq ∧ rel a b.
  Proof using Type.
    split.
    - intros (Hq & ag & Hag & Hrel). split; auto.
      inv Hag. simpl in Hrel. now rewrite @ura_unit_l in Hrel.
    - intros [Hq Hrel]. split; auto.
      exists a. split; auto. simpl. now rewrite @ura_unit_l.
  Qed.

  Lemma view_both_valid a b : ✓ (●V a ⋅ ◯V b) ↔ rel a b.
  Proof using Type. rewrite view_both_dfrac_valid. split; [naive_solver|done]. Qed.

  (** Inclusion *)
  Lemma view_auth_dfrac_included dq1 dq2 a1 a2 b :
    ●V{dq1} a1 ≼ ●V{dq2} a2 ⋅ ◯V b ↔ (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2.
  Proof using Type.
    split.
    - intros [[[[dqf agf]|] bf] [H _]%view_eq].
      + simpl in H. rewrite <-Some_op in H.
        inv H as [[Hq Hag]].
        split; [left; apply ra_included_l|].
        rewrite <-Ag_included. by exists agf.
      + inv H as [[Hq Hag]]; eauto.
    - intros [[[? ->]| ->] ->].
      + rewrite view_auth_dfrac_op, <-ra_assoc. apply ra_included_l.
      + apply ra_included_l.
  Qed.

  Lemma view_auth_included a1 a2 b :
    ●V a1 ≼ ●V a2 ⋅ ◯V b ↔ a1 = a2.
  Proof using Type. rewrite view_auth_dfrac_included. naive_solver. Qed.

  Lemma view_frag_included p a b1 b2 :
    ◯V b1 ≼ ●V{p} a ⋅ ◯V b2 ↔ b1 ≼ b2.
  Proof using Type.
    split.
    - intros [xf [_ Hb]%view_eq]; simpl in *.
      revert Hb. rewrite @ura_unit_l. by exists (view_frag_proj xf).
    - intros [bf ->]. rewrite ra_comm, view_frag_op, <-ra_assoc.
      apply ra_included_l.
  Qed.

  (** The weaker [view_both_included] lemmas below are a consequence of the
  [view_auth_included] and [view_frag_included] lemmas above. *)
  Lemma view_both_dfrac_included dq1 dq2 a1 a2 b1 b2 :
    ●V{dq1} a1 ⋅ ◯V b1 ≼ ●V{dq2} a2 ⋅ ◯V b2 ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2 ∧ b1 ≼ b2.
  Proof using Type.
    split.
    - intros. rewrite assoc; try apply _. split.
      + rewrite <-view_auth_dfrac_included. by etrans; [apply ra_included_l|].
      + rewrite <-view_frag_included. by etrans; [apply ra_included_r|].
    - intros (? & -> & bf & ->).
      rewrite (ra_comm b1), view_frag_op, ra_assoc.
      by apply ra_mono_r, view_auth_dfrac_included.
  Qed.

  Lemma view_both_included a1 a2 b1 b2 :
    ●V a1 ⋅ ◯V b1 ≼ ●V a2 ⋅ ◯V b2 ↔ a1 = a2 ∧ b1 ≼ b2.
  Proof using Type. rewrite view_both_dfrac_included. naive_solver. Qed.

  (** Updates *)

  (** Note that we quantify over a frame [bf], and since conceptually [rel n a b]
      means "[b] is a valid fragment to be part of [a]", there is another implicit
      frame quantification inside [rel] (usually because [rel] is defined via [≼]
      which contains an existential quantifier). The difference between the two
      frames is that the frame quantified inside [rel] may change but [bf] has
      to be preserved. It is not clear if it is possible to avoid this. *)
  Lemma view_updateP a b Pab :
    (∀ bf, rel a (b ⋅ bf) → ∃ a' b', Pab a' b' ∧ rel a' (b' ⋅ bf)) →
    ●V a ⋅ ◯V b ~~>: λ k, ∃ a' b', k = ●V a' ⋅ ◯V b' ∧ Pab a' b'.
  Proof using Type.
    intros Hup; apply ra_total_updateP.
    intros [[ag|] bf].
    { intros (Hdq & ? & ?). exfalso. eapply (exclusive_l _ _ Hdq). }
    intros (_ & a0 & <-%(inj Ag) & Hrel).
    simpl in Hrel. rewrite @ura_unit_l in Hrel.
    apply Hup in Hrel as (a' & b' & Hab' & Hrel).
    eexists; split.
    - naive_solver.
    - split; simpl; [done|].
      exists a'. split; auto. simpl.
      now rewrite @ura_unit_l.
  Qed.

  Lemma view_update a b a' b' :
    (∀ bf, rel a (b ⋅ bf) → rel a' (b' ⋅ bf)) →
    ●V a ⋅ ◯V b ~~> ●V a' ⋅ ◯V b'.
  Proof using Type.
    intros Hup.
    eapply ra_update_updateP, ra_updateP_weaken.
    { eapply view_updateP with (Pab := λ a b, a = a' ∧ b = b').
      naive_solver. }
    { naive_solver. }
  Qed.

  Lemma view_update_alloc a a' b' :
    (∀ bf, rel a bf → rel a' (b' ⋅ bf)) →
    ●V a ~~> ●V a' ⋅ ◯V b'.
  Proof using Type.
    intros Hup. rewrite <-(@ura_unit_r _ (●V a)).
    apply view_update. intros bf. rewrite @ura_unit_l. apply Hup.
  Qed.

  Lemma view_update_dealloc a b a' :
    (∀ bf, rel a (b ⋅ bf) → rel a' bf) →
    ●V a ⋅ ◯V b ~~> ●V a'.
  Proof using Type.
    intros Hup. rewrite <-(@ura_unit_r _ (●V a')).
    apply view_update. intros bf. rewrite @ura_unit_l. apply Hup.
  Qed.

  Lemma view_update_auth a a' :
    (∀ bf, rel a bf → rel a' bf) →
    ●V a ~~> ●V a'.
  Proof using Type.
    intros Hup. rewrite <-(@ura_unit_r _ (●V a)), <-(@ura_unit_r _ (●V a')).
    apply view_update. intros bf. rewrite !@ura_unit_l. apply Hup.
  Qed.

  Local Lemma view_updateP_auth_dfrac dq P a :
    dq ~~>: P →
    ●V{dq} a ~~>: λ k, ∃ dq', k = ●V{dq'} a ∧ P dq'.
  Proof using Type.
    intros Hupd. apply ra_total_updateP.
    intros [[[dq' ag]|] bf] [Hv ?].
    - destruct (Hupd (Some dq') Hv) as (dr&Hdr&Heq).
      eexists. split; first by eexists. done.
    - destruct (Hupd None Hv) as (dr&Hdr&Heq).
      eexists. split; first by eexists. done.
  Qed.

  Lemma view_update_auth_persist dq a : ●V{dq} a ~~> ●V□ a.
  Proof using Type.
    eapply (ra_update_lift_updateP (λ dq, view_auth dq a)).
    { intros; by apply view_updateP_auth_dfrac. }
    { apply dfrac_discard_update. }
  Qed.

  Lemma view_updateP_auth_unpersist a : ●V□ a ~~>: λ k, ∃ q, k = ●V{#q} a.
  Proof using Type.
    eapply ra_updateP_weaken.
    { eapply view_updateP_auth_dfrac, dfrac_undiscard_update. }
    naive_solver.
  Qed.

  Lemma view_updateP_both_unpersist a b : ●V□ a ⋅ ◯V b ~~>: λ k, ∃ q, k = ●V{#q} a ⋅ ◯V b.
  Proof using Type.
    eapply ra_updateP_weaken.
    { eapply ra_updateP_op'.
      { eapply view_updateP_auth_unpersist. }
      by eapply ra_update_updateP. }
    naive_solver.
  Qed.

  Lemma view_updateP_frag b P :
    (∀ a bf, rel a (b ⋅ bf) → ∃ b', P b' ∧ rel a (b' ⋅ bf)) →
    ◯V b ~~>: λ k, ∃ b', k = ◯V b' ∧ P b'.
  Proof using Type.
    rewrite !ra_total_updateP. unfold valid. simpl.
    unfold view_valid_instance. intros ? [[[dq ag]|] bf]; naive_solver.
  Qed.

  Lemma view_update_frag b b' :
    (∀ a bf, rel a (b ⋅ bf) → rel a (b' ⋅ bf)) →
    ◯V b ~~> ◯V b'.
  Proof using Type.
    rewrite !ra_total_update. unfold valid. simpl.
    unfold view_valid_instance. intros ? [[[dq ag]|] bf]; naive_solver.
  Qed.

  Lemma view_update_dfrac_alloc dq a b :
    (∀ bf, rel a bf → rel a (b ⋅ bf)) →
    ●V{dq} a ~~> ●V{dq} a ⋅ ◯V b.
  Proof using Type.
    intros Hup. apply ra_total_update. intros [[[p ag]|] bf]; simpl.
    - intros (Hq & a0 & Hag & Hrel). split; simpl; [done|].
      exists a0. split; [done|]. revert Hrel.
      assert (Ag a ≼ Ag a0) as <-%Ag_included.
      { by exists ag. }
      simpl. rewrite !@ura_unit_l. apply Hup.
    - intros (Hq & a0 & <-%(inj Ag) & Hrel). split; simpl; [done|].
      exists a; split; [done|]. revert Hrel.
      simpl. rewrite !@ura_unit_l. apply Hup.
  Qed.

  Lemma view_local_update a b0 b1 a' b0' b1' :
    (b0, b1) ~l~> (b0', b1') →
    (view_rel_holds _ _ rel a b0 → view_rel_holds _ _ rel a' b0') →
    (●V a ⋅ ◯V b0, ●V a ⋅ ◯V b1) ~l~> (●V a' ⋅ ◯V b0', ●V a' ⋅ ◯V b1').
  Proof using Type.
    rewrite !local_update_unital.
    intros Hup Hrel [[[[dq ag]|] bf]|] Hv%view_both_valid Heq;
    simpl in *.
    - inv Heq as [[Hdq Hag Hb]].
      exfalso. by apply (id_free_r (DfracOwn 1) dq).
    - inv Heq as [[Hb]]. rewrite !@ura_unit_l in Hb.
      split.
      + subst. by apply view_both_valid; auto.
      + apply view_eq; split; simpl; auto.
        rewrite !@ura_unit_l.
        apply Hup; auto. by eapply view_rel_valid.
    - inv Heq as [[Hb]]. rewrite !@ura_unit_l in Hb.
      split.
      + subst. by apply view_both_valid; auto.
      + apply view_eq; split; simpl; auto.
        rewrite @ura_unit_l, ra_comm.
        apply Hup; auto.
        * by eapply view_rel_valid.
        * now rewrite @ura_unit_r.
  Qed.

End ra.
