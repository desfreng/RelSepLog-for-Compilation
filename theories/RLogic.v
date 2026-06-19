From RSL Require Import Prelude.

From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.

(** * Logic Definition *)

Definition rprop : Type :=
  memory -> memory -> Prop.

(** ** Entailement *)

Local Definition rprop_entails_def (P Q: rprop) : Prop :=
  ∀ mt ms, P mt ms -> Q mt ms.

Local Definition rprop_entails_aux : seal (@rprop_entails_def).
Proof. by eexists. Qed.
Definition rprop_entails := unseal rprop_entails_aux.
Local Lemma rprop_entails_unseal : @rprop_entails = @rprop_entails_def.
Proof. exact: seal_eq. Qed.

Local Instance rprop_equiv : Equiv rprop :=
  fun P Q => rprop_entails P Q ∧ rprop_entails Q P.

(** ** Empty Heap *)

Local Definition rprop_empty_def : rprop :=
  fun mt ms => mt = ∅ ∧ ms = ∅.

Local Definition rprop_empty_aux : seal (@rprop_empty_def).
Proof. by eexists. Qed.
Definition rprop_empty := unseal rprop_empty_aux.
Local Lemma rprop_empty_unseal : @rprop_empty = @rprop_empty_def.
Proof. exact: seal_eq. Qed.

(** ** Pure lifting *)

Local Definition rprop_pure_def (P: Prop) : rprop :=
  fun _ _ => P.

Local Definition rprop_pure_aux : seal (@rprop_pure_def).
Proof. by eexists. Qed.
Definition rprop_pure := unseal rprop_pure_aux.
Local Lemma rprop_pure_unseal : @rprop_pure = @rprop_pure_def.
Proof. exact: seal_eq. Qed.

(** ** Logical Connectives *)

(** *** And *)

Local Definition rprop_and_def (P Q: rprop) : rprop :=
  fun mt ms => P mt ms ∧ Q mt ms.

Local Definition rprop_and_aux : seal (@rprop_and_def).
Proof. by eexists. Qed.
Definition rprop_and := unseal rprop_and_aux.
Local Lemma rprop_and_unseal : @rprop_and = @rprop_and_def.
Proof. exact: seal_eq. Qed.

(** *** Or *)

Local Definition rprop_or_def (P Q: rprop) : rprop :=
  fun mt ms => P mt ms ∨ Q mt ms.

Local Definition rprop_or_aux : seal (@rprop_or_def).
Proof. by eexists. Qed.
Definition rprop_or := unseal rprop_or_aux.
Local Lemma rprop_or_unseal : @rprop_or = @rprop_or_def.
Proof. exact: seal_eq. Qed.

(** *** Implication *)

Local Definition rprop_impl_def (P Q: rprop) : rprop :=
  fun mt ms => P mt ms -> Q mt ms.

Local Definition rprop_impl_aux : seal (@rprop_impl_def).
Proof. by eexists. Qed.
Definition rprop_impl := unseal rprop_impl_aux.
Local Lemma rprop_impl_unseal : @rprop_impl = @rprop_impl_def.
Proof. exact: seal_eq. Qed.

(** *** Forall *)

Local Definition rprop_forall_def : ∀ X (f: X -> rprop), rprop :=
  fun X f mt ms => ∀ x, f x mt ms.

Local Definition rprop_forall_aux : seal (@rprop_forall_def).
Proof. by eexists. Qed.
Definition rprop_forall := unseal rprop_forall_aux.
Local Lemma rprop_forall_unseal : @rprop_forall = @rprop_forall_def.
Proof. exact: seal_eq. Qed.

(** *** Exist *)

Local Definition rprop_exist_def : ∀ X (f: X -> rprop), rprop :=
  fun X f mt ms => ∃ x, f x mt ms.

Local Definition rprop_exist_aux : seal (@rprop_exist_def).
Proof. by eexists. Qed.
Definition rprop_exist := unseal rprop_exist_aux.
Local Lemma rprop_exist_unseal : @rprop_exist = @rprop_exist_def.
Proof. exact: seal_eq. Qed.

(** *** Separating conjunction *)

Local Definition rprop_sep_def (P Q: rprop) : rprop :=
  fun mt ms =>
    ∃ mtP msP mtQ msQ,
      mtP ##ₘ mtQ ∧
      msP ##ₘ msQ ∧
      mtP ∪ mtQ = mt ∧
      msP ∪ msQ = ms ∧
      P mtP msP ∧
      Q mtQ msQ.

Local Definition rprop_sep_aux : seal (@rprop_sep_def).
Proof. by eexists. Qed.
Definition rprop_sep := unseal rprop_sep_aux.
Local Lemma rprop_sep_unseal : @rprop_sep = @rprop_sep_def.
Proof. exact: seal_eq. Qed.

(** *** Separating implication *)

Local Definition rprop_wand_def (P Q: rprop) : rprop :=
  fun mt ms =>
    ∀ mtP msP,
  mt ##ₘ mtP ->
  ms ##ₘ msP ->
  P mtP msP ->
  Q (mt ∪ mtP) (ms ∪ msP).

Local Definition rprop_wand_aux : seal (@rprop_wand_def).
Proof. by eexists. Qed.
Definition rprop_wand := unseal rprop_wand_aux.
Local Lemma rprop_wand_unseal : @rprop_wand = @rprop_wand_def.
Proof. exact: seal_eq. Qed.

(** *** Persistent connective *)

Local Definition rprop_persistently_def (P: rprop) : rprop :=
 rprop_pure (rprop_entails rprop_empty P).

Local Definition rprop_persistently_aux : seal (@rprop_persistently_def).
Proof. by eexists. Qed.
Definition rprop_persistently := unseal rprop_persistently_aux.
Local Lemma rprop_persistently_unseal : @rprop_persistently = @rprop_persistently_def.
Proof. exact: seal_eq. Qed.

(** *** Later connective *)

Local Definition rprop_later_def (P: rprop) : rprop := P.

Local Definition rprop_later_aux : seal (@rprop_later_def).
Proof. by eexists. Qed.
Definition rprop_later := unseal rprop_later_aux.
Local Lemma rprop_later_unseal : @rprop_later = @rprop_later_def.
Proof. exact: seal_eq. Qed.

(** ** Unfold tactic  *)

Local Ltac unseal :=
  unfold equiv, rprop_equiv;
  rewrite
    ?rprop_entails_unseal
    ?rprop_empty_unseal
    ?rprop_pure_unseal
    ?rprop_and_unseal
    ?rprop_or_unseal
    ?rprop_impl_unseal
    ?rprop_forall_unseal
    ?rprop_exist_unseal
    ?rprop_sep_unseal
    ?rprop_wand_unseal
    ?rprop_empty_unseal
    ?rprop_persistently_unseal
    ?rprop_later_unseal;
  simpl.

(** * Properties *)

(** ** Entailement properties *)

Instance rprop_equiv_equiv : @Equivalence rprop (≡).
Proof. unseal; constructor; now firstorder. Qed.

Local Instance rprop_dist : Dist rprop :=
  fun _ => equiv.

Local Instance rprop_entails_preorder : PreOrder rprop_entails.
Proof. unseal; constructor; now firstorder. Qed.

Local Lemma rprop_equiv_entails P Q :
  (rprop_equiv P Q) <-> (rprop_entails P Q) ∧ (rprop_entails Q P).
Proof. unseal; now firstorder. Qed.

(** ** Pure lifting Properties *)

Local Lemma rprop_pure_ne : Proper (iff ==> equiv) rprop_pure.
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_pure_intro Φ P :
  Φ -> rprop_entails P (rprop_pure Φ).
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_pure_elim Φ P :
  (Φ -> rprop_entails (rprop_pure True) P) ->
  rprop_entails (rprop_pure Φ) P.
Proof. unseal; now firstorder. Qed.

(** ** Logical Connectives *)

(** *** And *)

Local Lemma rprop_and_ne : Proper (equiv ==> equiv ==> equiv) rprop_and.
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_and_intro P Q R :
  rprop_entails P Q ->
  rprop_entails P R ->
  rprop_entails P (rprop_and Q R).
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_and_elim_l P Q : rprop_entails (rprop_and P Q) P.
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_and_elim_r P Q : rprop_entails (rprop_and P Q) Q.
Proof. unseal; now firstorder. Qed.

(** *** Or *)

Local Lemma rprop_or_ne : Proper (equiv ==> equiv ==> equiv) rprop_or.
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_or_intro_l P Q : rprop_entails P (rprop_or P Q).
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_or_intro_r P Q : rprop_entails Q (rprop_or P Q).
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_or_elim P Q R :
  rprop_entails P R ->
  rprop_entails Q R ->
  rprop_entails (rprop_or P Q) R.
Proof. unseal; now firstorder. Qed.

(** *** Implication *)

Local Lemma rprop_impl_ne : Proper (equiv ==> equiv ==> equiv) rprop_impl.
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_impl_intro P Q R :
  rprop_entails (rprop_and P Q) R ->
  rprop_entails P (rprop_impl Q R).
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_impl_elim P Q R :
  rprop_entails P (rprop_impl Q R) ->
  rprop_entails (rprop_and P Q) R.
Proof. unseal; now firstorder. Qed.

(** *** Forall *)

Local Lemma rprop_forall_ne A :
  Proper (pointwise_relation A equiv ==> equiv) (rprop_forall A).
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_forall_intro A P (Ψ: A -> rprop) :
  (∀ a, rprop_entails P (Ψ a)) ->
  rprop_entails P (rprop_forall A Ψ).
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_forall_elim A (Ψ: A -> rprop) a :
  rprop_entails (rprop_forall A Ψ) (Ψ a).
Proof. unseal; now firstorder. Qed.

(** *** Exist *)

Local Lemma rprop_exist_ne A :
  Proper (pointwise_relation A equiv ==> equiv) (rprop_exist A).
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_exist_intro A (Ψ: A -> rprop)  a :
  rprop_entails (Ψ a) (rprop_exist A Ψ).
Proof. unseal; now firstorder. Qed.

Local Lemma rprop_exist_elim A (Ψ: A -> rprop) P :
  (∀ a, rprop_entails (Ψ a) P) ->
  rprop_entails (rprop_exist A Ψ) P.
Proof. unseal; now firstorder. Qed.

(** *** Separating conjunction *)

Local Lemma rprop_sep_ne : Proper (equiv ==> equiv ==> equiv) rprop_sep.
Proof.
  unseal.
  intros P Q HPQ R S HRS.
  split; intros mt ms.
  - intros (mtP & msP & mtR & msR & ? & ? & ? & ? & HP & HR).
    exists mtP, msP, mtR, msR. repeat split; auto; now firstorder.
  - intros (mtQ & msQ & mtS & msS & ? & ? & ? & ? & HQ & HS).
    exists mtQ, msQ, mtS, msS. repeat split; auto; now firstorder.
Qed.

Local Lemma rprop_sep_mono P P' Q Q' :
  rprop_entails P Q ->
  rprop_entails P' Q' ->
  rprop_entails (rprop_sep P P') (rprop_sep Q Q').
Proof.
  unseal.
  intros H H' mt ms.
  intros (mtP & msP & mtP' & msP' & ? & ? & ? & ? & HP & HP').
  exists mtP, msP, mtP', msP'. repeat split; now auto.
Qed.

Local Lemma rprop_sep_emp_intro P :
  rprop_entails P (rprop_sep rprop_empty P).
Proof.
  unseal.
  intros mt ms HP.
  exists ∅, ∅, mt, ms. repeat split.
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
  - apply map_empty_union.
  - apply map_empty_union.
  - assumption.
Qed.

Local Lemma rprop_sep_emp_elim P :
  rprop_entails (rprop_sep rprop_empty P) P.
Proof.
  unseal.
  intros mt ms (? & ? & ? & ? & ? & ? & <- & <- & [-> ->] & HP).
  now rewrite !(map_empty_union _).
Qed.

Local Lemma rprop_sep_comm P Q :
  rprop_entails (rprop_sep P Q) (rprop_sep Q P).
Proof.
  unseal.
  intros mt ms (mtP & msP & mtQ & msQ & Ht & Hs & Hcupt & Hcups & HP & HQ).
  subst.
  exists mtQ, msQ, mtP, msP.
  repeat split.
  - solve_map_disjoint.
  - solve_map_disjoint.
  - apply map_union_comm. solve_map_disjoint.
  - apply map_union_comm. solve_map_disjoint.
  - assumption.
  - assumption.
Qed.

Local Lemma rprop_sep_assoc P Q R :
  rprop_entails (rprop_sep (rprop_sep P Q) R) (rprop_sep P (rprop_sep Q R)).
Proof.
  unseal.
  intros mt ms HPQR.
  destruct HPQR as (mtPQ & msPQ & mtR & msR & ? & ? & <- & <- & HPQ & HR).
  destruct HPQ as (mtP & msP & mtQ & msQ & ? & ? & <- & <- & HP & HQ).
  rewrite <- !(map_union_assoc _).
  decompose_map_disjoint.
  do 4 eexists.
  repeat split.
  - solve_map_disjoint.
  - solve_map_disjoint.
  - assumption.
  - do 4 eexists.
    repeat split; assumption.
Qed.

(** *** Separating implication *)

Local Lemma rprop_wand_ne : Proper (equiv ==> equiv ==> equiv) rprop_wand.
Proof.
  unseal.
  intros P Q HPQ R S HRS.
  split; intros mt ms.
  - intros H mtQ msQ ? ? HQ.
    apply HRS. apply H; auto.
    now apply HPQ.
  - intros H mtP msP ? ? HP.
    apply HRS. apply H; auto.
    now apply HPQ.
Qed.

Local Lemma rprop_wand_intro P Q R :
  rprop_entails (rprop_sep P Q) R ->
  rprop_entails P (rprop_wand Q R).
Proof.
  unseal.
  intros H mt ms HP mtQ msQ HQ ? ?.
  apply H.
  exists mt, ms, mtQ, msQ. repeat split; easy.
Qed.

Local Lemma rprop_wand_elim P Q R :
  rprop_entails P (rprop_wand Q R) ->
  rprop_entails (rprop_sep P Q) R.
Proof.
  unseal.
  intros H mt ms (mtP & msP & mtQ & msQ & ? & ? & <- & <- & HP & HQ).
  apply H in HP.
  apply HP in HQ; easy.
Qed.

(** ** BI Mixin *)

Definition rprop_bi_mixin :
  BiMixin
    rprop_entails
    rprop_empty
    rprop_pure
    rprop_and
    rprop_or
    rprop_impl
    rprop_forall
    rprop_exist
    rprop_sep
    rprop_wand.
Proof.
  constructor.
  - exact: rprop_entails_preorder.
  - exact: rprop_equiv_entails.
  - unfold dist, rprop_dist; intros _.
    exact: rprop_pure_ne.
  - unfold dist, rprop_dist; intros _.
    exact: rprop_and_ne.
  - unfold dist, rprop_dist; intros _.
    exact: rprop_or_ne.
  - unfold dist, rprop_dist; intros _.
    exact: rprop_impl_ne.
  - unfold dist, rprop_dist; intros A _.
    exact: rprop_forall_ne.
  - unfold dist, rprop_dist; intros A _.
    exact: rprop_exist_ne.
  - unfold dist, rprop_dist; intros _.
    exact: rprop_sep_ne.
  - unfold dist, rprop_dist; intros _.
    exact: rprop_wand_ne.
  - exact: rprop_pure_intro.
  - exact: rprop_pure_elim.
  - exact: rprop_and_elim_l.
  - exact: rprop_and_elim_r.
  - exact: rprop_and_intro.
  - exact: rprop_or_intro_l.
  - exact: rprop_or_intro_r.
  - exact: rprop_or_elim.
  - exact: rprop_impl_intro.
  - exact: rprop_impl_elim.
  - exact: rprop_forall_intro.
  - exact: rprop_forall_elim.
  - exact: rprop_exist_intro.
  - exact: rprop_exist_elim.
  - exact: rprop_sep_mono.
  - exact: rprop_sep_emp_intro.
  - exact: rprop_sep_emp_elim.
  - exact: rprop_sep_comm.
  - exact: rprop_sep_assoc.
  - exact: rprop_wand_intro.
  - exact: rprop_wand_elim.
Qed.

Definition rprop_bi_persistently_mixin :
  BiPersistentlyMixin
    rprop_entails
    rprop_empty
    rprop_and
    rprop_exist
    rprop_sep
    rprop_persistently.
Proof.
  pose proof rprop_bi_mixin as H. revert H.
  apply bi_persistently_mixin_discrete.
  - done.
  - unseal. intros Q Φ H.
    destruct (H ∅ ∅) as [x HΦ]; try done.
    exists x.
    now intros mt ms [-> ->].
  - intros P.
    unseal.
    unfold rprop_persistently_def. unseal.
    easy.
Qed.

(** ** Later connective *)

Definition rprop_bi_later_mixin :
  BiLaterMixin
    rprop_entails
    rprop_pure
    rprop_or
    rprop_impl
    rprop_forall
    rprop_exist
    rprop_sep
    rprop_persistently
    rprop_later.
Proof.
  pose proof rprop_bi_mixin as H. revert H.
  apply bi_later_mixin_id.
  unseal. easy.
Qed.

(** ** Rprop is a BI *)

Canonical Structure rlogic : bi :=
  {|
    bi_car := rprop;
    bi_dist := rprop_dist;
    bi_equiv := rprop_equiv;
    bi_entails := rprop_entails;
    bi_emp := rprop_empty;
    bi_pure := rprop_pure;
    bi_and := rprop_and;
    bi_or := rprop_or;
    bi_impl := rprop_impl;
    bi_forall := rprop_forall;
    bi_exist := rprop_exist;
    bi_sep := rprop_sep;
    bi_wand := rprop_wand;
    bi_persistently := rprop_persistently;
    bi_later := rprop_later;
    bi_ofe_mixin := discrete_ofe_mixin rprop_equiv_equiv;
    bi_cofe_aux := discrete_cofe rprop_equiv_equiv;
    bi_bi_mixin := rprop_bi_mixin;
    bi_bi_persistently_mixin := rprop_bi_persistently_mixin;
    bi_bi_later_mixin := rprop_bi_later_mixin;
  |}.

(** ** Memory Connectives *)

Local Definition mem_assert addr x (m: memory) : Prop :=
  ∃ loc, val_to_loc addr = Some loc ∧ m = {[loc := x]}.

Definition rprop_mem_t_assert addr x : rprop :=
  fun mt ms => mem_assert addr x mt ∧ ms = ∅.

Definition rprop_mem_s_assert addr x : rprop :=
  fun mt ms => mt = ∅ ∧ mem_assert addr x ms.

Notation "l '→ₜ' v" :=
  (rprop_mem_t_assert l%positive v%Z)
    (at level 70, no associativity, format "l →ₜ v") : bi_scope.

Notation "l '→ₛ' v" :=
  (rprop_mem_s_assert l%positive v%Z)
    (at level 70, no associativity, format "l →ₛ v") : bi_scope.

Notation "addrt 'ₜ⟨' P '⟩ₛ' addrs" :=
  (∃ vt vs, addrt →ₜ vt ∗ addrs →ₛ vs ∗ ⌜P vt vs⌝)%I
    (at level 70, no associativity) : bi_scope.

Notation "addrs 'ₛ⟨' P '⟩ₜ' addrt" :=
  (∃ vt vs, addrt →ₜ vt ∗ addrs →ₛ vs ∗ ⌜P vt vs⌝)%I
    (at level 70, no associativity) : bi_scope.

Notation "addrt 'ₜ~ₛ' addrs" :=
  (∃ v, addrt →ₜ v ∗ addrs →ₛ v)%I
    (at level 70, no associativity) : bi_scope.

Notation "addrs 'ₛ~ₜ' addrt" :=
  (∃ v, addrt →ₜ v ∗ addrs →ₛ v)%I
    (at level 70, no associativity) : bi_scope.
