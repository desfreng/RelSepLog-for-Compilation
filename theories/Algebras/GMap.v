From RSL Require Import Prelude.
From RSL.Algebras Require Import GSet.
From RSL.Algebras Require Import RA Updates LocalUpdates ProofModeClasses GSet.

From stdpp Require Export gmap.
From Stdlib Require Import ssreflect.

(* RA *)
Section ra.
  Context `{Countable K} {A : ra}.
  Implicit Types m : gmap K A.

  Local Instance gmap_unit_instance : Unit (gmap K A) := (∅ : gmap K A).
  Local Instance gmap_op_instance : Op (gmap K A) := merge op.
  Local Instance gmap_pcore_instance : PCore (gmap K A) := λ m, Some (omap pcore m).
  Local Instance gmap_valid_instance : Valid (gmap K A) := λ m, ∀ i, ✓ (m !! i).

  Lemma gmap_op m1 m2 : m1 ⋅ m2 = merge op m1 m2.
  Proof using Type. done. Qed.

  Lemma lookup_op m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
  Proof using Type.
    rewrite !gmap_op lookup_merge. by destruct (m1 !! i), (m2 !! i).
  Qed.

  Lemma lookup_core m i : core m !! i = core (m !! i).
  Proof using Type. by apply lookup_omap. Qed.

  Lemma lookup_included (m1 m2 : gmap K A) : m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.
  Proof using Type.
    split.
    { by intros [m Hm] i; exists (m !! i); rewrite <-lookup_op, Hm. }
    revert m2. induction m1 as [|i x m Hi IH] using map_ind=> m2 Hm.
    { exists m2. rewrite gmap_op. apply map_eq.
      intros i. rewrite lookup_merge lookup_empty.
      by destruct (m2 !! i). }
    destruct (IH (delete i m2)) as [m2' Hm2'].
    { intros j. pose proof (Hm j) as Hj. revert Hj.
      destruct (decide (i = j)) as [->|].
      - intros _. rewrite Hi. apply @ura_unit_least.
      - rewrite lookup_insert_ne; auto. now rewrite lookup_delete_ne. }
    destruct (Hm i) as [my Hi']; simplify_map_eq.
    exists (partial_alter (λ _, my) i m2').
    apply map_eq; intros j. destruct (decide (i = j)) as [->|].
    - by rewrite Hi' lookup_op lookup_insert_eq lookup_partial_alter_eq.
    - rewrite map_eq_iff in Hm2'. specialize (Hm2' j).
      revert Hm2'.
      rewrite !lookup_op lookup_delete_ne; auto.
      rewrite lookup_insert_ne; auto. rewrite lookup_partial_alter_ne; auto.
  Qed.

  Lemma gmap_ra_mixin : RaMixin (gmap K A).
  Proof using Type.
    apply ra_total_mixin.
    - intros x. by eexists.
    - intros x y z. apply map_eq. intros i. now rewrite !lookup_op ra_assoc.
    - intros x y. apply map_eq. intros i. now rewrite !lookup_op ra_comm.
    - intros x. apply map_eq. intros i.
      rewrite lookup_op lookup_core.
      destruct (x !! i) as [r|] eqn:He; simpl; auto.
      unfold core. simpl.
      destruct (pcore r) as [cr|]eqn:Hcore.
      + rewrite <-Some_op. f_equal. now apply ra_pcore_l.
      + easy.
    - intros x. apply map_eq. intros i.
      rewrite !lookup_core.
      destruct (x !! i) as [r|] eqn:Hcx; auto.
      unfold core. simpl in *.
      destruct (pcore r) as [cr|] eqn:Hcr; auto.
      by apply ra_pcore_idemp with (x := r).
    - intros x y. rewrite !lookup_included. intros Hlt i.
      rewrite !lookup_core.
      specialize (Hlt i).
      now apply ra_core_mono.
    - intros x y Hv i.
      apply ra_valid_op_l with (y := y !! i).
      by rewrite <-lookup_op.
  Qed.

  Canonical Structure gmapRA := Ra (gmap K A) gmap_ra_mixin.

  Lemma gmap_ura_mixin : URaMixin (gmap K A).
  Proof using Type.
    split.
    - intros i. unfold ε, gmap_unit_instance. by rewrite lookup_empty.
    - intros m. apply map_eq. intros i.
      rewrite lookup_op.
      unfold ε, gmap_unit_instance.
      by rewrite lookup_empty @ura_unit_l.
    - f_equal.
  Qed.

  Canonical Structure gmapURA := URa (gmap K A) gmap_ura_mixin.

  Global Instance gmap_op_empty_l_L : LeftId (=@{gmap K A}) ∅ op.
  Proof using Type. apply _. Qed.

  Global Instance gmap_op_empty_r : RightId (=@{gmap K A}) ∅ op.
  Proof using Type. apply _. Qed.

End ra.

Global Arguments gmapRA _ {_ _} _.
Global Arguments gmapURA _ {_ _} _.

Section properties.
  Context `{Countable K} {A : ra}.
  Implicit Types m : gmap K A.
  Implicit Types i : K.
  Implicit Types x y : A.

  Lemma lookup_opM m1 mm2 i : (m1 ⋅? mm2) !! i = m1 !! i ⋅ (mm2 ≫= (.!! i)).
  Proof using Type.
    destruct mm2; simpl; rewrite ?lookup_op; auto.
    rewrite @ura_unit_r; auto.
  Qed.

  Lemma lookup_valid_Some m i x : ✓ m → m !! i = Some x → ✓ x.
  Proof using Type.
    intros Hm Hi. specialize (Hm i). revert Hm. by rewrite Hi.
  Qed.

  Lemma insert_valid m i x : ✓ x → ✓ m → ✓ <[i:=x]>m.
  Proof using Type. by intros ?? j; destruct (decide (i = j)); simplify_map_eq. Qed.

  Lemma singleton_validN i x : ✓ ({[ i := x ]} : gmap K A) ↔ ✓ x.
  Proof using Type.
    split.
    - intros Hi. eapply lookup_valid_Some; eauto. apply lookup_singleton_eq.
    - intros Hx. apply insert_valid; first done. by apply @ura_unit_valid.
  Qed.

  Lemma delete_valid m i : ✓ m → ✓ (delete i m).
  Proof using Type. intros Hm j; destruct (decide (i = j)); by simplify_map_eq. Qed.

  Lemma insert_singleton_op m i x : m !! i = None → <[i:=x]> m = {[ i := x ]} ⋅ m.
  Proof using Type.
    intros Hi; apply map_eq=> j; destruct (decide (i = j)) as [->|].
    - by rewrite @lookup_op lookup_insert_eq lookup_singleton_eq Hi @ura_unit_r.
    - by rewrite @lookup_op lookup_insert_ne // lookup_singleton_ne // @ura_unit_l.
  Qed.

  Lemma singleton_core (i : K) (x : A) cx :
    pcore x = Some cx → core {[ i := x ]} =@{gmap K A} {[ i := cx ]}.
  Proof using Type. apply omap_singleton_Some. Qed.

  Lemma singleton_core_total `{!RaTotal A} (i : K) (x : A) :
    core {[ i := x ]} =@{gmap K A} {[ i := core x ]}.
  Proof using Type. apply singleton_core. by rewrite ra_pcore_core. Qed.
  Lemma singleton_op (i : K) (x y : A) :
    {[ i := x ]} ⋅ {[ i := y ]} =@{gmap K A} {[ i := x ⋅ y ]}.
  Proof using Type. by apply (merge_singleton _ _ _ x y). Qed.

  Global Instance singleton_is_op i a a1 a2 :
    IsOp a a1 a2 → IsOp' ({[ i := a ]} : gmap K A) {[ i := a1 ]} {[ i := a2 ]}.
  Proof using Type. intros ->. by rewrite <-singleton_op. Qed.

  Lemma gmap_core_id m : (∀ i x, m !! i = Some x → CoreId x) → CoreId m.
  Proof using Type.
    intros Hcore; apply core_id_total; simpl. apply map_eq. intros i.
    rewrite lookup_core. destruct (m !! i) as [x|] eqn:Hix; rewrite ?Hix; [|done].
    by apply Hcore with i.
  Qed.

  Global Instance gmap_core_id' m : (∀ x : A, CoreId x) → CoreId m.
  Proof using Type. auto using gmap_core_id. Qed.

  Global Instance gmap_singleton_core_id i (x : A) :
    CoreId x → CoreId {[ i := x ]}.
  Proof using Type. intros. by apply core_id_total, singleton_core. Qed.

  Lemma singleton_included_l m i x :
    {[ i := x ]} ≼ m ↔ ∃ y, m !! i = Some y ∧ Some x ≼ Some y.
  Proof using Type.
    split.
    - intros [m' Hm]. rewrite map_eq_iff in Hm. specialize (Hm i).
      rewrite @lookup_op lookup_singleton_eq in Hm.
      exists (x ⋅? m' !! i). rewrite <- Some_op_opM; split; auto.
      by eexists.
    - intros (y & Hi & [mz Hy]). exists (partial_alter (λ _, mz) i m).
      apply map_eq. intros j; destruct (decide (i = j)) as [->|].
      + by rewrite @lookup_op lookup_singleton_eq lookup_partial_alter_eq Hi.
      + by rewrite @lookup_op lookup_singleton_ne // lookup_partial_alter_ne //
          @ura_unit_l.
  Qed.

  Lemma singleton_included_exclusive_l m i x :
    Exclusive x → ✓ m →
    {[ i := x ]} ≼ m ↔ m !! i = Some x.
  Proof using Type.
    intros ? Hm. rewrite singleton_included_l. split.
    - intros (y&?&->%(Some_included_exclusive _)); eauto using lookup_valid_Some.
    - intros Hi. exists x. split; auto. reflexivity.
  Qed.

  Lemma singleton_included i x y :
    {[ i := x ]} ≼ ({[ i := y ]} : gmap K A) ↔ Some x ≼ Some y.
  Proof using Type.
    rewrite singleton_included_l. split.
    - intros (y'&Hi&?). rewrite lookup_singleton_eq in Hi. by rewrite Hi.
    - intros ?. exists y. by rewrite lookup_singleton_eq.
  Qed.

  Lemma singleton_included_total `{!RaTotal A}  i x y :
    {[ i := x ]} ≼ ({[ i := y ]} : gmap K A) ↔ x ≼ y.
  Proof using Type. rewrite singleton_included Some_included_total; by auto. Qed.

  Lemma singleton_included_mono i x y :
    x ≼ y → {[ i := x ]} ≼ ({[ i := y ]} : gmap K A).
  Proof using Type.
    intros Hincl. apply singleton_included, Some_included_mono. done.
  Qed.

  Global Instance singleton_cancelable i x :
    Cancelable (Some x) → Cancelable {[ i := x ]}.
  Proof using Type.
    intros ? m1 m2 Hv EQ. simpl in *. apply map_eq. intros j.
    specialize (Hv j). rewrite map_eq_iff in EQ. specialize (EQ j).
    revert Hv EQ. rewrite !lookup_op.
    destruct (decide (i = j)) as [->|].
    - rewrite lookup_singleton_eq. by apply cancelable.
    - by rewrite lookup_singleton_ne; auto; rewrite !@ura_unit_l.
  Qed.

  Global Instance gmap_cancelable (m : gmap K A) :
    (∀ x : A, IdFree x) → (∀ x : A, Cancelable x) → Cancelable m.
  Proof using Type.
    intros ?? m1 m2 Hv EQ. simpl in *. apply map_eq. intros i.
    apply (cancelable (m !! i)); simpl; rewrite <-!@lookup_op; auto.
    by rewrite EQ.
  Qed.

  Lemma insert_op m1 m2 i x y :
    <[i:=x ⋅ y]>(m1 ⋅ m2) = <[i:=x]>m1 ⋅ <[i:=y]>m2.
  Proof using Type.
    apply map_eq. intros j.
    rewrite @lookup_op !lookup_insert. destruct (decide (i = j)).
    - easy.
    - apply lookup_op.
  Qed.

  Lemma insert_updateP (P : A → Prop) (Q : gmap K A → Prop) m i x :
    x ~~>: P →
    (∀ y, P y → Q (<[i:=y]>m)) →
    <[i:=x]>m ~~>: Q.
  Proof using Type.
    intros Hx%option_updateP' HP; apply ra_total_updateP=> mf Hm.
    destruct (Hx (Some (mf !! i))) as ([y|]&?&?); try done.
    { by generalize (Hm i); rewrite @lookup_op; simplify_map_eq. }
    exists (<[i:=y]> m); split; first by auto.
    intros j.
    specialize (Hm j). revert Hm. rewrite !@lookup_op.
    destruct (decide (i = j)); simplify_map_eq/=; auto.
  Qed.

  Lemma insert_updateP' (P : A → Prop) m i x :
  x ~~>: P → <[i:=x]>m ~~>: λ m', ∃ y, m' = <[i:=y]>m ∧ P y.
  Proof using Type. eauto using insert_updateP. Qed.

  Lemma insert_update m i x y : x ~~> y → <[i:=x]>m ~~> <[i:=y]>m.
  Proof using Type. rewrite !ra_update_updateP; eauto using insert_updateP with subst. Qed.

  Lemma singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) i x :
    x ~~>: P → (∀ y, P y → Q {[ i := y ]}) → {[ i := x ]} ~~>: Q.
  Proof using Type. apply insert_updateP. Qed.
  Lemma singleton_updateP' (P : A → Prop) i x :
    x ~~>: P → {[ i := x ]} ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
  Proof using Type. apply insert_updateP'. Qed.
  Lemma singleton_update i (x y : A) : x ~~> y → {[ i := x ]} ~~> {[ i := y ]}.
  Proof using Type. apply insert_update. Qed.

  Lemma delete_update m i : m ~~> delete i m.
  Proof using Type.
    apply ra_total_update=> mf Hm j; destruct (decide (i = j)); subst.
    - specialize (Hm j). revert Hm.
      rewrite !@lookup_op lookup_delete_eq @ura_unit_l.
      apply ra_valid_op_r.
    - specialize (Hm j). revert Hm.
      by rewrite !@lookup_op lookup_delete_ne.
  Qed.

  Lemma gmap_op_union m1 m2 : m1 ##ₘ m2 → m1 ⋅ m2 = m1 ∪ m2.
  Proof using Type.
    intros Hm. simpl. rewrite gmap_op. apply map_disjoint_merge_as_union; done.
  Qed.

  Lemma gmap_op_valid_disjoint m1 m2 :
    ✓ (m1 ⋅ m2) → (∀ k x, m1 !! k = Some x → Exclusive x) → m1 ##ₘ m2.
  Proof using Type.
    unfold Exclusive. intros Hvalid Hexcl k.
    specialize (Hvalid k). rewrite @lookup_op in Hvalid. specialize (Hexcl k).
    destruct (m1 !! k), (m2 !! k); [|done..].
    rewrite <-Some_op, Some_valid in Hvalid. naive_solver.
  Qed.

  Lemma dom_op m1 m2 : dom (m1 ⋅ m2) = dom m1 ∪ dom m2.
  Proof using Type.
    apply set_eq=> i; rewrite elem_of_union !elem_of_dom.
    unfold is_Some; setoid_rewrite lookup_op.
    destruct (m1 !! i), (m2 !! i); naive_solver.
  Qed.

  Lemma dom_included m1 m2 : m1 ≼ m2 → dom m1 ⊆ dom m2.
  Proof using Type.
    rewrite lookup_included=>? i; rewrite !elem_of_dom. by apply is_Some_included.
  Qed.

  Section freshness.
    Context `{!Infinite K}.

    Lemma alloc_updateP_strong_dep (Q : gmap K A → Prop) (I : K → Prop) m (f : K → A) :
      pred_infinite I →
      (∀ i, m !! i = None → I i → ✓ (f i)) →
      (∀ i, m !! i = None → I i → Q (<[i:=f i]>m)) → m ~~>: Q.
    Proof using Type.
      move=> /(pred_infinite_set I (C:=gset K)) HP ? HQ.
      apply ra_total_updateP. intros mf Hm.
      destruct (HP (dom (m ⋅ mf))) as [i [Hi1 Hi2]].
      assert (m !! i = None).
      { eapply not_elem_of_dom. revert Hi2.
        rewrite dom_op not_elem_of_union. naive_solver. }
      exists (<[i:=f i]>m); split.
      - by apply HQ.
      - rewrite insert_singleton_op //.
        rewrite -ra_assoc -insert_singleton_op.
        + by eapply not_elem_of_dom.
        + apply insert_valid; auto.
    Qed.

    Lemma alloc_updateP_strong (Q : gmap K A → Prop) (I : K → Prop) m x :
      pred_infinite I →
      ✓ x → (∀ i, m !! i = None → I i → Q (<[i:=x]>m)) → m ~~>: Q.
    Proof using Type.
      move=> HP ? HQ. eapply (alloc_updateP_strong_dep _ _ _ (λ _, x)); eauto.
    Qed.

    Lemma alloc_updateP (Q : gmap K A → Prop) m x :
      ✓ x → (∀ i, m !! i = None → Q (<[i:=x]>m)) → m ~~>: Q.
    Proof using Type*.
      move=>??.
      eapply (alloc_updateP_strong _ (λ _, True));
        eauto using pred_infinite_True.
    Qed.

    Lemma alloc_updateP_cofinite (Q : gmap K A → Prop) (J : gset K) m x :
      ✓ x → (∀ i, m !! i = None → i ∉ J → Q (<[i:=x]>m)) → m ~~>: Q.
    Proof using Type*.
      eapply alloc_updateP_strong.
      apply (pred_infinite_set (C:=gset K)).
      intros E. exists (fresh (J ∪ E)).
      apply not_elem_of_union, is_fresh.
    Qed.

    (* Variants without the universally quantified Q, for use in case that is an evar. *)
    Lemma alloc_updateP_strong_dep' m (f : K → A) (I : K → Prop) :
      pred_infinite I →
      (∀ i, m !! i = None → I i → ✓ (f i)) →
      m ~~>: λ m', ∃ i, I i ∧ m' = <[i:=f i]>m ∧ m !! i = None.
    Proof using Type. eauto using alloc_updateP_strong_dep. Qed.

    Lemma alloc_updateP_strong' m x (I : K → Prop) :
      pred_infinite I →
      ✓ x → m ~~>: λ m', ∃ i, I i ∧ m' = <[i:=x]>m ∧ m !! i = None.
    Proof using Type. eauto using alloc_updateP_strong. Qed.

    Lemma alloc_updateP' m x :
      ✓ x → m ~~>: λ m', ∃ i, m' = <[i:=x]>m ∧ m !! i = None.
    Proof using Type*. eauto using alloc_updateP. Qed.

    Lemma alloc_updateP_cofinite' m x (J : gset K) :
      ✓ x → m ~~>: λ m', ∃ i, (i ∉ J) ∧ m' = <[i:=x]>m ∧ m !! i = None.
    Proof using Type*. eauto using alloc_updateP_cofinite. Qed.
  End freshness.

  Lemma alloc_unit_singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) u i :
    ✓ u → LeftId (=) u (⋅) →
    u ~~>: P → (∀ y, P y → Q {[ i := y ]}) → ∅ ~~>: Q.
  Proof using Type.
    intros ?? Hx HQ. apply ra_total_updateP=> gf Hg.
    destruct (Hx (gf !! i)) as (y&?&Hy).
    { move:(Hg i). rewrite !left_id.
      case: (gf !! i)=>[x|]; rewrite /= ?left_id //. }
    exists {[ i := y ]}; split; first by auto.
    intros i'; destruct (decide (i' = i)) as [->|].
    - rewrite lookup_op lookup_singleton_eq.
      move:Hy; case: (gf !! i)=>[x|]; rewrite /= ?right_id //.
    - move:(Hg i'). rewrite !@lookup_op lookup_singleton_ne; auto.
  Qed.

  Lemma alloc_unit_singleton_updateP' (P: A → Prop) u i :
    ✓ u → LeftId (=) u (⋅) →
    u ~~>: P → ∅ ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
  Proof using Type. eauto using alloc_unit_singleton_updateP. Qed.

  Lemma alloc_unit_singleton_update (u : A) i (y : A) :
    ✓ u → LeftId (=) u (⋅) → u ~~> y → (∅:gmap K A) ~~> {[ i := y ]}.
  Proof using Type.
    rewrite !ra_update_updateP;
      eauto using alloc_unit_singleton_updateP with subst.
  Qed.

  Lemma gmap_local_update m1 m2 m1' m2' :
    (∀ i, (m1 !! i, m2 !! i) ~l~> (m1' !! i, m2' !! i)) →
    (m1, m2) ~l~> (m1', m2').
  Proof using Type.
    intros Hupd. apply local_update_unital=> mf Hmv Hm.
    rewrite map_eq_iff. apply forall_and_distr=> i. rewrite @lookup_op -ra_opM_fmap_Some.
    apply Hupd; simpl; first done. by rewrite Hm lookup_op ra_opM_fmap_Some.
  Qed.

  Lemma alloc_local_update m1 m2 i x :
    m1 !! i = None → ✓ x → (m1,m2) ~l~> (<[i:=x]>m1, <[i:=x]>m2).
  Proof using Type.
    intros Hi ?. apply gmap_local_update=> j.
    destruct (decide (i = j)) as [->|]; last by rewrite !lookup_insert_ne.
    rewrite !lookup_insert_eq Hi. by apply alloc_option_local_update.
  Qed.

  Lemma alloc_singleton_local_update m i x :
    m !! i = None → ✓ x → (m,∅) ~l~> (<[i:=x]>m, {[ i:=x ]}).
  Proof using Type. apply alloc_local_update. Qed.

  Lemma insert_local_update m1 m2 i x y x' y' :
    m1 !! i = Some x → m2 !! i = Some y →
    (x, y) ~l~> (x', y') →
    (m1, m2) ~l~> (<[i:=x']>m1, <[i:=y']>m2).
  Proof using Type.
    intros Hi1 Hi2 Hup. apply gmap_local_update=> j.
    destruct (decide (i = j)) as [->|]; last by rewrite !lookup_insert_ne.
    rewrite !lookup_insert_eq Hi1 Hi2. by apply option_local_update.
  Qed.

  Lemma singleton_local_update_any m i y x' y' :
    (∀ x, m !! i = Some x → (x, y) ~l~> (x', y')) →
    (m, {[ i := y ]}) ~l~> (<[i:=x']>m, {[ i := y' ]}).
  Proof using Type.
    intros. apply gmap_local_update=> j.
    destruct (decide (i = j)) as [->|]; last by rewrite !lookup_insert_ne.
    rewrite !lookup_singleton_eq lookup_insert_eq.
    destruct (m !! j); first by eauto using option_local_update.
    apply local_update_total_valid=> _ _ /option_included; naive_solver.
  Qed.

  Lemma singleton_local_update m i x y x' y' :
    m !! i = Some x →
    (x, y) ~l~> (x', y') →
    (m, {[ i := y ]}) ~l~> (<[i:=x']>m, {[ i := y' ]}).
  Proof using Type.
    intros Hmi ?. apply singleton_local_update_any.
    intros x2. rewrite Hmi=>[=<-]. done.
  Qed.

  Lemma delete_local_update m1 m2 i x `{!Exclusive x} :
    m2 !! i = Some x → (m1, m2) ~l~> (delete i m1, delete i m2).
  Proof using Type.
    intros Hi. apply gmap_local_update=> j.
    destruct (decide (i = j)) as [->|]; last by rewrite !lookup_delete_ne.
    rewrite !lookup_delete_eq Hi. by apply delete_option_local_update.
  Qed.

  Lemma delete_singleton_local_update m i x `{!Exclusive x} :
    (m, {[ i := x ]}) ~l~> (delete i m, ∅).
  Proof using Type.
    rewrite -(delete_singleton_eq i x).
    by eapply delete_local_update, lookup_singleton_eq.
  Qed.

  Lemma delete_local_update_cancelable m1 m2 i mx `{!Cancelable mx} :
    m1 !! i = mx → m2 !! i = mx →
    (m1, m2) ~l~> (delete i m1, delete i m2).
  Proof using Type.
    intros Hi1 Hi2. apply gmap_local_update=> j.
    destruct (decide (i = j)) as [->|]; last by rewrite !lookup_delete_ne.
    rewrite !lookup_delete_eq Hi1 Hi2. by apply delete_option_local_update_cancelable.
  Qed.

  Lemma delete_singleton_local_update_cancelable m i x `{!Cancelable (Some x)} :
    m !! i = Some x → (m, {[ i := x ]}) ~l~> (delete i m, ∅).
  Proof using Type.
    intros. rewrite -(delete_singleton_eq i x).
    apply (delete_local_update_cancelable m _ i (Some x));
      [done|by rewrite lookup_singleton_eq].
  Qed.

  Lemma gmap_fmap_mono {B : ra} (f : A → B) m1 m2 :
    (∀ x y, x ≼ y → f x ≼ f y) → m1 ≼ m2 → fmap f m1 ≼ fmap f m2.
  Proof using Type.
    intros ??. rewrite !@lookup_included=> i.
    rewrite !lookup_fmap. apply option_fmap_mono; auto.
    by apply lookup_included.
  Qed.

  (* Lemma big_opM_singletons m : *)
  (*   ([^op map] k ↦ x ∈ m, {[ k := x ]}) = m. *)
  (* Proof using Type. *)
  (*   (* We are breaking the big_opM abstraction here. The reason is that [map_ind] *)
  (*      is too weak: we need an induction principle that visits all the keys in the *)
  (*      right order, namely the order in which they appear in map_to_list.  Here, *)
  (*      we achieve this by unfolding [big_opM] and doing induction over that list *)
  (*      instead. *) *)
  (*   rewrite big_op.big_opM_unseal /big_op.big_opM_def -{2}(list_to_map_to_list m). *)
  (*   assert (NoDup (map_to_list m).*1) as Hnodup by apply NoDup_fst_map_to_list. *)
  (*   revert Hnodup. induction (map_to_list m) as [|[k x] l IH]; csimpl; first done. *)
  (*   intros [??]%NoDup_cons. rewrite IH //. *)
  (*   rewrite insert_singleton_op ?not_elem_of_list_to_map_1 //. *)
  (* Qed. *)

  (* Lemma big_opS_gset_to_gmap (X : gset K) (a : A) : *)
  (*   ([^op set] x ∈ X, {[ x := a ]}) = gset_to_gmap a X. *)
  (* Proof using Type. *)
  (*   induction X as [|x X ? IH] using set_ind_L. *)
  (*   { rewrite big_opS_empty gset_to_gmap_empty //. } *)
  (*   rewrite big_opS_insert //. *)
  (*   rewrite gset_to_gmap_union_singleton. *)
  (*   rewrite insert_singleton_op; [|by rewrite lookup_gset_to_gmap_None]. *)
  (*   by rewrite IH. *)
  (* Qed. *)

  (* Lemma big_opS_gset_to_gmap_L `{!LeibnizEquiv A} (X : gset K) (a : A) : *)
  (*   ([^op set] x ∈ X, {[ x := a ]}) = gset_to_gmap a X. *)
  (* Proof using Type. apply leibniz_equiv, big_opS_gset_to_gmap. Qed. *)

End properties.

Section unital_properties.
  Context `{Countable K} {A : ura}.
  Implicit Types m : gmap K A.
  Implicit Types i : K.
  Implicit Types x y : A.

  Lemma insert_alloc_local_update m1 m2 i x x' y' :
    m1 !! i = Some x → m2 !! i = None →
    (x, ε) ~l~> (x', y') →
    (m1, m2) ~l~> (<[i:=x']>m1, <[i:=y']>m2).
  Proof using Type.
    intros Hi1 Hi2 Hup. apply local_update_unital=> mf Hm1v Hm.
    assert (Hm' : ∀ i, m1 !! i = (m2 ⋅ mf) !! i) by (apply map_eq_iff; apply Hm).
    assert (mf !! i = Some x) as Hif.
    { move: (Hm' i). by rewrite lookup_op Hi1 Hi2 left_id. }
    destruct (Hup  (mf !! i)) as [Hx'v Hx'eq].
    { move: (Hm1v i). by rewrite Hi1. }
    { by rewrite Hif -(inj_iff Some) -Some_op_opM -Some_op @ura_unit_l. }
    split.
    - by apply insert_valid.
    - simpl in Hx'eq. by rewrite -(insert_id mf i x) // -insert_op -Hm Hx'eq Hif.
  Qed.
End unital_properties.
