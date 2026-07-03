From RSL Require Import Prelude.
From RSL.Algebras Require Export RA ProofModeClasses.

(** ** Unit Ressource Algebra *)
Section unit.
  Local Instance unit_valid_instance : Valid unit := fun x => True.
  Local Instance unit_pcore_instance : PCore unit := fun x => Some x.
  Local Instance unit_op_instance : Op unit := fun x y => tt.
  Local Instance unit_unit_instance : Unit unit := tt.

  Lemma unit_ra_mixin : RaMixin unit.
  Proof.
    constructor; try easy.
    - intros [] [] H. easy.
    - intros [] [] [] H. exists tt. split. { easy. }
      by exists tt.
  Qed.

  Lemma unit_ura_mixin : URaMixin unit.
  Proof. constructor; try easy; by intros []. Qed.

  Canonical Structure unitRA : ra := Ra unit unit_ra_mixin.
  Canonical Structure unitURA : ura := URa unit unit_ura_mixin.

  Global Instance unit_core_id (x : unit) : CoreId x.
  Proof. by constructor. Qed.

  Global Instance unit_cancelable (x : ()) : Cancelable x.
  Proof. now intros [] []. Qed.

End unit.

(** ** Empty Ressource Algebra *)
Section empty.
  Local Instance Empty_set_valid_instance : Valid Empty_set := fun x => False.
  Local Instance Empty_set_pcore_instance : PCore Empty_set := fun x => Some x.
  Local Instance Empty_set_op_instance : Op Empty_set := fun x y => x.

  Lemma Empty_set_ra_mixin : RaMixin Empty_set.
  Proof. by constructor. Qed.

  Canonical Structure Empty_setRA : ra := Ra Empty_set Empty_set_ra_mixin.

  Global Instance Empty_set_core_id (x : Empty_set) : CoreId x.
  Proof. by constructor. Qed.

  Global Instance Empty_set_cancelable (x : Empty_set) : Cancelable x.
  Proof. by intros []. Qed.

End empty.

(** ** Product *)
Section prod.
  Context (A B : ra).
  Local Arguments pcore _ _ !_ /.
  Local Arguments ra_pcore _ !_/.

  Local Instance prod_op_instance : Op (A * B) :=
    fun x y => (fst x ⋅ fst y, snd x ⋅ snd y).

  Local Instance prod_pcore_instance : PCore (A * B) :=
    fun x =>
      match pcore (fst x), pcore (snd x) with
      | Some c1, Some c2 => Some (c1, c2)
      | _, _ => None
      end.

  Local Arguments prod_pcore_instance !_ /.

  Local Instance prod_valid_instance : Valid (A * B) :=
    fun x => ✓ (fst x) ∧ ✓ (snd x).

  Lemma prod_pcore_Some (x cx : A * B) :
    pcore x = Some cx
     <-> pcore (fst x) = Some (fst cx) ∧ pcore (snd x) = Some (snd cx).
  Proof using Type.
    destruct x as [a b]. simpl.
    destruct (pcore a), (pcore b); try by intuition.
    destruct cx. simpl. split.
    - intros H. by inv H.
    - intros [H1 H2]. by inv H1.
  Qed.

  Lemma prod_included (x y : A * B) : x ≼ y <-> fst x ≼ fst y ∧ snd x ≼ snd y.
  Proof using Type.
    split.
    - intros [z ->]. simpl. split; apply ra_included_l.
    - intros [[z1 H1] [z2 H2]]. destruct x, y; simpl in *.
      exists (z1,z2). now subst.
  Qed.

  Definition prod_ra_mixin : RaMixin (A * B).
  Proof using Type.
    split; try apply _.
    - intros [] [] []; unfold op, prod_op_instance; simpl.
      now rewrite !ra_assoc.
    - intros [] []; unfold op, prod_op_instance; simpl.
      rewrite ra_comm. f_equal. apply ra_comm.
    - intros x cx [H1 H2]%prod_pcore_Some.
      destruct x, cx; unfold op, prod_op_instance; simpl in *;
      f_equal; by apply ra_pcore_l.
    - intros x cx [H1 H2]%prod_pcore_Some.
      rewrite prod_pcore_Some. by split; eapply ra_pcore_idemp.
    - intros x y cx [Hlt1 Hlt2]%prod_included [Hcx1 Hcx2]%prod_pcore_Some.
      destruct (ra_pcore_mono _ _ _ Hlt1 Hcx1) as (cy1 & Hcy1 & Hy1).
      destruct (ra_pcore_mono _ _ _ Hlt2 Hcx2) as (cy2 & Hcy2 & Hy2).
      exists (cy1, cy2).
      by rewrite prod_pcore_Some, prod_included.
    - intros x y [H1 H2]; split; eapply ra_valid_op_l; apply H1 || apply H2.
  Qed.

  Canonical Structure prodRA := Ra (prod A B) prod_ra_mixin.

  Lemma pair_op (a a' : A) (b b' : B) : (a ⋅ a', b ⋅ b') = (a, b) ⋅ (a', b').
  Proof using Type. done. Qed.

  Lemma pair_valid (a : A) (b : B) : ✓ (a, b) ↔ ✓ a ∧ ✓ b.
  Proof using Type. done. Qed.

  Lemma pair_included (a a' : A) (b b' : B) :
    (a, b) ≼ (a', b') ↔ a ≼ a' ∧ b ≼ b'.
  Proof using Type. apply prod_included. Qed.

  Lemma pair_pcore (a : A) (b : B) :
    pcore (a, b) = c1 ← pcore a; c2 ← pcore b; Some (c1, c2).
  Proof using Type. done. Qed.

  Lemma pair_core `{!RaTotal A, !RaTotal B} (a : A) (b : B) :
    core (a, b) = (core a, core b).
  Proof using Type.
    unfold core. unfold pcore at 1. simpl.
    by rewrite (ra_pcore_core a), (ra_pcore_core b).
  Qed.

  Global Instance prod_ra_total : RaTotal A -> RaTotal B -> RaTotal prodRA.
  Proof using Type.
    intros H1 H2 [a b]. destruct (H1 a) as [ca ?], (H2 b) as [cb ?].
    exists (ca,cb); by simplify_option_eq.
  Qed.

  Lemma pair_core_id x y :
    CoreId x → CoreId y → CoreId (x,y).
  Proof using Type. by unfold CoreId; rewrite prod_pcore_Some. Qed.

  Global Instance pair_exclusive_l x y : Exclusive x → Exclusive (x,y).
  Proof using Type. by intros ?[][?%exclusive_l]. Qed.

  Global Instance pair_exclusive_r x y : Exclusive y → Exclusive (x,y).
  Proof using Type. by intros ?[][??%exclusive_l]. Qed.

  Global Instance pair_cancelable x y :
    Cancelable x → Cancelable y → Cancelable (x, y).
  Proof using Type.
    intros ? ? [] [] [H1 H2] He. inv He as [[Hl Hr]]; simpl in *.
    eapply cancelable in Hl; auto.
    eapply cancelable in Hr; auto.
    congruence.
  Qed.

  Global Instance pair_id_free_l x y : IdFree x → IdFree (x,y).
  Proof using Type.
    intros Hx [a b] [? _] He.
    inv He. apply (Hx a); eauto.
  Qed.

  Global Instance pair_id_free_r x y : IdFree y → IdFree (x,y).
  Proof using Type.
    intros Hy [a b] [_ ?] He.
    inv He. apply (Hy b); eauto.
  Qed.
End prod.

Global Hint Extern 4 (CoreId _) =>
  notypeclasses refine (pair_core_id _ _ _ _) : typeclass_instances.


Section prod_unit.
  Context {A B : ura}.

  Local Instance prod_unit_instance `{Unit A, Unit B} : Unit (A * B) := (ε, ε).

  Lemma prod_ura_mixin : URaMixin (A * B).
  Proof using Type.
    split.
    - split; simpl; apply ura_unit_valid.
    - intros [a b]. unfold ε, op. simpl.
      unfold prod_op_instance, prod_unit_instance. simpl.
      now rewrite !@ura_unit_l.
    - rewrite prod_pcore_Some; split; apply (core_id _).
  Qed.

  Canonical Structure prodURA := URa (prod A B) prod_ura_mixin.

  Lemma pair_split (a : A) (b : B) : (a, b) = (a, ε) ⋅ (ε, b).
  Proof using Type.
    unfold op. simpl. unfold prod_op_instance. simpl.
    now rewrite @ura_unit_l, @ura_unit_r.
  Qed.

  Lemma pair_op_1 (a a': A) : (a ⋅ a', ε) =@{A*B} (a, ε) ⋅ (a', ε).
  Proof using Type.
    unfold op. simpl. unfold prod_op_instance. simpl.
    now rewrite @ura_unit_l.
  Qed.

  Lemma pair_op_2 (b b': B) :
    (ε, b ⋅ b') =@{A*B} (ε, b) ⋅ (ε, b').
  Proof using Type.
    unfold op. simpl. unfold prod_op_instance. simpl.
    now rewrite @ura_unit_l.
  Qed.
End prod_unit.

Section option.
  Context (A : ra).

  Implicit Types a b : A.
  Implicit Types ma mb : option A.

  Local Instance option_valid_instance : Valid (option A) :=
    fun ma =>
      match ma with Some a => ✓ a | None => True end.

  Local Instance option_pcore_instance : PCore (option A) :=
    fun ma => Some (match ma with Some a => pcore a | None => None end).

  Local Instance option_op_instance : Op (option A) :=
    union_with (λ a b, Some (a ⋅ b)).

  Local Instance option_unit_instance : Unit (option A) := None.

  Definition Some_valid a : ✓ Some a ↔ ✓ a := reflexivity _.

  Definition Some_op a b : Some (a ⋅ b) = Some a ⋅ Some b := eq_refl.

  Lemma Some_core `{!RaTotal A} a : Some (core a) = core (Some a).
  Proof using Type.
    by unfold core; simpl; destruct (ra_total a) as [? ->].
  Qed.

  Lemma pcore_Some a : pcore (Some a) = Some (pcore a).
  Proof using Type. done. Qed.

  Lemma Some_op_opM a ma : Some a ⋅ ma = Some (a ⋅? ma).
  Proof using Type. by destruct ma. Qed.

  Lemma option_included ma mb :
    ma ≼ mb <-> ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ (a = b ∨ a ≼ b).
  Proof using Type.
    split.
    - intros [mc Hmc].
      destruct ma as [a|]; [right|by left].
      destruct mb as [b|]; [exists a, b|destruct mc; inv Hmc].
      destruct mc as [c|]; inversion_clear Hmc; split_and?; auto.
      setoid_subst. right. apply ra_included_l.
    - intros [->|(a&b&->&->&[Hc|[c Hc]])].
      + exists mb. by destruct mb.
      + exists None. subst. by constructor.
      + exists (Some c); subst. by constructor.
  Qed.

  Lemma option_included_total `{RaTotal A} ma mb :
    ma ≼ mb ↔ ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ a ≼ b.
  Proof using Type.
    rewrite option_included. split; last naive_solver.
    intros [->|(a&b&->&->&[Hab|?])]; [by eauto| |by eauto 10].
    right. exists a, b. by rewrite Hab at 3.
  Qed.

  Lemma option_ra_mixin : RaMixin (option A).
  Proof using Type.
    constructor.
    - by intros [a|] [b|] [c|]; unfold op; simpl; auto; rewrite ra_assoc.
    - by intros [a|] [b|]; unfold op; simpl; auto; rewrite ra_comm.
    - intros [a|] cx H; injection H as H; subst.
      + destruct (pcore a) eqn:?; unfold op; simpl; f_equal; eauto using ra_pcore_l.
      + easy.
    - intros [a|] cx H; injection H as H; subst; auto.
      destruct (pcore a) as [ca|] eqn:Hca; simpl; eauto.
      by rewrite pcore_Some, (ra_pcore_idemp _ _ Hca).
    - intros x y cx [ -> | (a & b & Ha & Hb & [ H | Hle])]%option_included Hcx;
        injection Hcx as <-.
      + destruct y as [b|].
        * exists (pcore b). rewrite pcore_Some. split; auto.
          apply option_included; now left.
        * exists None. split; auto.
          apply option_included; now left.
      + subst x y. destruct (pcore a) as [ca|] eqn:Hca.
        * exists (Some ca). rewrite pcore_Some. split; try congruence.
          apply option_included. right.
          exists ca, ca. now split; auto.
        * rewrite pcore_Some. exists (pcore b).
          split; auto. apply option_included; by left.
      + subst x y. destruct (pcore a) as [ca|] eqn:Hca.
        * destruct (ra_pcore_mono a b ca) as (cb & Hcb & Hc); auto.
          exists (Some cb). rewrite pcore_Some, Hcb. split; auto.
          apply option_included. right.
          exists ca, cb. now split; auto.
        * rewrite pcore_Some. exists (pcore b).
          split; auto. apply option_included; by left.
    - by intros [] []; unfold valid; simpl; eauto using ra_valid_op_l.
  Qed.

  Canonical Structure optionRA :=
    Ra (option A) option_ra_mixin.

  Lemma option_ura_mixin : URaMixin optionRA.
  Proof using Type. split; [done|  |done]. by intros []. Qed.

  Canonical Structure optionURA :=
    URa (option A) option_ura_mixin.

  Lemma op_None ma mb : ma ⋅ mb = None <-> ma = None ∧ mb = None.
  Proof using Type.
    destruct ma, mb; naive_solver.
  Qed.

  Lemma op_is_Some ma mb : is_Some (ma ⋅ mb) <-> is_Some ma ∨ is_Some mb.
  Proof using Type.
    rewrite <-!not_eq_None_Some, op_None. destruct ma, mb; naive_solver.
  Qed.

  Lemma op_None_l ma : None ⋅ ma = ma.
  Proof using Type. destruct ma; easy. Qed.

  Lemma op_None_r ma : ma ⋅ None = ma.
  Proof using Type. destruct ma; easy. Qed.

  Lemma ra_opM_opM_assoc a mb mc : a ⋅? mb ⋅? mc = a ⋅? (mb ⋅ mc).
  Proof using Type. destruct mb, mc; simpl; by rewrite <-?ra_assoc. Qed.

  Lemma ra_opM_opM_swap a mb mc : a ⋅? mb ⋅? mc = a ⋅? mc ⋅? mb.
  Proof using Type. by rewrite !ra_opM_opM_assoc, ra_comm. Qed.

  Lemma ra_opM_fmap_Some ma1 ma2 : ma1 ⋅? (Some <$> ma2) = ma1 ⋅ ma2.
  Proof using Type. by destruct ma1, ma2. Qed.

  Global Instance Some_core_id a : CoreId a -> CoreId (Some a).
  Proof using Type.
    unfold CoreId. intros H.
    unfold pcore. simpl. unfold option_pcore_instance. congruence.
  Qed.

  Global Instance option_core_id ma : (∀ x : A, CoreId x) -> CoreId ma.
  Proof using Type. intros. destruct ma; apply _. Qed.

  Lemma exclusive_Some_l a `{!Exclusive a} mb : ✓ (Some a ⋅ mb) → mb = None.
  Proof using Type. destruct mb; last done. intros []%(exclusive_l a). Qed.

  Lemma exclusive_Some_r a `{!Exclusive a} mb : ✓ (mb ⋅ Some a) → mb = None.
  Proof using Type. rewrite ra_comm. by apply exclusive_Some_l. Qed.

  Lemma Some_included a b : Some a ≼ Some b ↔ a = b ∨ a ≼ b.
  Proof using Type. rewrite option_included; naive_solver. Qed.

  Lemma Some_included_1 a b : Some a ≼ Some b → a = b ∨ a ≼ b.
  Proof using Type. rewrite Some_included. auto. Qed.

  Lemma Some_included_2 a b : a = b ∨ a ≼ b → Some a ≼ Some b.
  Proof using Type. rewrite Some_included. auto. Qed.

  Lemma Some_included_mono a b : a ≼ b → Some a ≼ Some b.
  Proof using Type. rewrite Some_included. auto. Qed.

  Lemma Some_included_refl a b : a = b → Some a ≼ Some b.
  Proof using Type. rewrite Some_included. auto. Qed.

  Lemma Some_included_is_Some x mb : Some x ≼ mb → is_Some mb.
  Proof using Type. rewrite option_included. naive_solver. Qed.

  Lemma Some_included_opM a b : Some a ≼ Some b ↔ ∃ mc, b = a ⋅? mc.
  Proof using Type.
    unfold included. split.
    - intros [[] H]; inv H.
      + now eexists (Some _).
      + now eexists None.
    - intros [[] H]; inv H; simpl.
      + now eexists (Some _).
      + now eexists None.
  Qed.

  Lemma ra_valid_Some_included a b : ✓ a → Some b ≼ Some a → ✓ b.
  Proof using Type. apply (ra_valid_included (Some _) (Some _)). Qed.

  Lemma Some_included_total `{!RaTotal A} a b : Some a ≼ Some b ↔ a ≼ b.
  Proof using Type.
    rewrite Some_included. split; [|by eauto]. by intros [->|?].
  Qed.

  Lemma Some_included_exclusive a `{!Exclusive a} b :
    Some a ≼ Some b → ✓ b → a = b.
  Proof using Type.
    intros [-> | ?]%Some_included; auto.
    intros Hb.
    eapply exclusive_included in Hb; eauto. contradiction.
  Qed.

  Lemma is_Some_included ma mb : ma ≼ mb → is_Some ma → is_Some mb.
  Proof using Type.
    rewrite <-!not_eq_None_Some, option_included. naive_solver.
  Qed.

  Global Instance cancelable_None : Cancelable None.
  Proof using Type.
    by intros [] []; unfold op; simpl.
  Qed.

  Global Instance cancelable_Some a :
    IdFree a → Cancelable a → Cancelable (Some a).
  Proof using Type.
    intros Hirr Hcan [b|] [c|] Hv Heq; inv Heq as [He].
    - apply cancelable in He; auto. congruence.
    - destruct (Hirr b); auto. by eapply (ra_valid_op_l a b).
    - destruct (Hirr c); auto.
    - done.
  Qed.

  Global Instance option_cancelable (ma : option A) :
    (∀ a : A, IdFree a) → (∀ a : A, Cancelable a) → Cancelable ma.
  Proof using Type. destruct ma; apply _. Qed.

End option.

Section option_prod.
  Context {A B : ra}.
  Implicit Types a : A.
  Implicit Types b : B.

  Lemma Some_pair_included a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ Some b1 ≼ Some b2.
  Proof using Type.
    rewrite !Some_included. intros [H|[??]%prod_included]; eauto;
      inv H; eauto.
  Qed.

  Lemma Some_pair_included_l a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2.
  Proof using Type. intros. eapply Some_pair_included. done. Qed.

  Lemma Some_pair_included_r a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some b1 ≼ Some b2.
  Proof using Type. intros. eapply Some_pair_included. done. Qed.

  Lemma Some_pair_included_total_1 `{!RaTotal A} a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → a1 ≼ a2 ∧ Some b1 ≼ Some b2.
  Proof using Type.
    intros ?%Some_pair_included. by rewrite <-(Some_included_total _ a1).
  Qed.

  Lemma Some_pair_included_total_2 `{!RaTotal B} a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ b1 ≼ b2.
  Proof using Type.
    intros ?%Some_pair_included. by rewrite <-(Some_included_total _ b1).
  Qed.
End option_prod.

Lemma option_fmap_mono {A B : ra} (f : A → B) (ma mb : option A) :
  (∀ a b, a ≼ b → f a ≼ f b) →
  ma ≼ mb → f <$> ma ≼ f <$> mb.
Proof.
  intros ?. rewrite !option_included; intros [->|(a&b&->&->&?)]; naive_solver.
Qed.

(* FromOp *)
(* TODO: Worst case there could be a lot of backtracking on these instances,
try to refactor. *)

Global Instance is_op_pair {A B : ra} (a b1 b2 : A) (a' b1' b2' : B) :
  IsOp a b1 b2 → IsOp a' b1' b2' → IsOp' (a, a') (b1,b1') (b2,b2').
Proof. intros -> ->. constructor. Qed.

Global Instance is_op_pair_core_id_l {A B : ra} (a : A) (a' b1' b2' : B) :
  CoreId a → IsOp a' b1' b2' → IsOp' (a,a') (a,b1') (a,b2').
Proof.
  intros ? ->. unfold IsOp', IsOp, op.
  simpl. unfold prod_op_instance. simpl.
  by rewrite <-core_id_dup.
Qed.

Global Instance is_op_pair_core_id_r {A B : ra} (a b1 b2 : A) (a' : B) :
  CoreId a' → IsOp a b1 b2 → IsOp' (a,a') (b1,a') (b2,a').
Proof.
  intros ? ->. unfold IsOp', IsOp, op.
  simpl. unfold prod_op_instance. simpl.
  by rewrite <-core_id_dup.
Qed.

Global Instance is_op_Some {A : ra} (a : A) b1 b2 :
  IsOp a b1 b2 → IsOp' (Some a) (Some b1) (Some b2).
Proof. intros ->. constructor. Qed.
