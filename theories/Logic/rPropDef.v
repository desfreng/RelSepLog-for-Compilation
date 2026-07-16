From RSL Require Import Prelude.

From RSL.Commons Require Import Memory.

From iris.bi Require Import notation.

(** * Logic Definition *)

Record rPropDef : Type :=
  {
    rProp_holds : memory -> memory -> Prop;
  }.

Section rPropDef_def.
  Local Coercion rProp_holds : rPropDef >-> Funclass.

  (** ** Entailement *)

  Local Definition rPropDef_entails_def (P Q: rPropDef) : Prop :=
    ∀ mt ms, P mt ms -> Q mt ms.

  Local Definition rPropDef_entails_aux : seal (@rPropDef_entails_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_entails := unseal rPropDef_entails_aux.
  Local Lemma rPropDef_entails_unseal : @rPropDef_entails = @rPropDef_entails_def.
  Proof using Type. by apply seal_eq. Qed.

  Global Instance rPropDef_equiv : Equiv rPropDef :=
    fun P Q => rPropDef_entails P Q ∧ rPropDef_entails Q P.

  (** ** Pure lifting *)

  Local Definition rPropDef_pure_def (P: Prop) : rPropDef :=
    {| rProp_holds _ _ := P |}.

  Local Definition rPropDef_pure_aux : seal (@rPropDef_pure_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_pure := unseal rPropDef_pure_aux.
  Local Lemma rPropDef_pure_unseal : @rPropDef_pure = @rPropDef_pure_def.
  Proof using Type. by apply seal_eq. Qed.

  (** ** Empty Predicate *)

  Local Definition rPropDef_empty_def : rPropDef :=
    {| rProp_holds mt ms := mt = ∅ ∧ ms = ∅ |}.

  Local Definition rPropDef_empty_aux : seal (@rPropDef_empty_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_empty := unseal rPropDef_empty_aux.
  Local Lemma rPropDef_empty_unseal : @rPropDef_empty = @rPropDef_empty_def.
  Proof using Type. by apply seal_eq. Qed.

  (** ** Logical Connectives *)

  (** *** And *)

  Local Definition rPropDef_and_def (P Q: rPropDef) : rPropDef :=
    {| rProp_holds mt ms := P mt ms ∧ Q mt ms |}.

  Local Definition rPropDef_and_aux : seal (@rPropDef_and_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_and := unseal rPropDef_and_aux.
  Local Lemma rPropDef_and_unseal : @rPropDef_and = @rPropDef_and_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Or *)

  Local Definition rPropDef_or_def (P Q: rPropDef) : rPropDef :=
    {| rProp_holds mt ms := P mt ms ∨ Q mt ms |}.

  Local Definition rPropDef_or_aux : seal (@rPropDef_or_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_or := unseal rPropDef_or_aux.
  Local Lemma rPropDef_or_unseal : @rPropDef_or = @rPropDef_or_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Implication *)

  Local Definition rPropDef_impl_def (P Q: rPropDef) : rPropDef :=
    {| rProp_holds mt ms := P mt ms -> Q mt ms |}.

  Local Definition rPropDef_impl_aux : seal (@rPropDef_impl_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_impl := unseal rPropDef_impl_aux.
  Local Lemma rPropDef_impl_unseal : @rPropDef_impl = @rPropDef_impl_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Forall **)

  Local Definition rPropDef_forall_def : ∀ X (f: X -> rPropDef), rPropDef :=
    fun X f => {| rProp_holds mt ms := ∀ x, f x mt ms |}.

  Local Definition rPropDef_forall_aux : seal (@rPropDef_forall_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_forall := unseal rPropDef_forall_aux.
  Local Lemma rPropDef_forall_unseal : @rPropDef_forall = @rPropDef_forall_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Exist *)

  Local Definition rPropDef_exist_def : ∀ X (f: X -> rPropDef), rPropDef :=
    fun X f => {| rProp_holds mt ms := ∃ x, f x mt ms |}.

  Local Definition rPropDef_exist_aux : seal (@rPropDef_exist_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_exist := unseal rPropDef_exist_aux.
  Local Lemma rPropDef_exist_unseal : @rPropDef_exist = @rPropDef_exist_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Separating conjunction *)

  Local Definition rPropDef_sep_def (P Q: rPropDef) : rPropDef :=
    {| rProp_holds mt ms :=
        ∃ mtP msP mtQ msQ,
          mtP ##ₘ mtQ ∧
          msP ##ₘ msQ ∧
          mtP ∪ mtQ = mt ∧
          msP ∪ msQ = ms ∧
          P mtP msP ∧
          Q mtQ msQ
    |}.

  Local Definition rPropDef_sep_aux : seal (@rPropDef_sep_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_sep := unseal rPropDef_sep_aux.
  Local Lemma rPropDef_sep_unseal : @rPropDef_sep = @rPropDef_sep_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Separating implication *)

  Local Definition rPropDef_wand_def (P Q: rPropDef) : rPropDef :=
    {| rProp_holds mt ms :=
        ∀ mtP msP,
         mtP ##ₘ mt ->
         msP ##ₘ ms ->
         P mtP msP ->
         Q (mt ∪ mtP) (ms ∪ msP)
    |}.

  Local Definition rPropDef_wand_aux : seal (@rPropDef_wand_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_wand := unseal rPropDef_wand_aux.
  Local Lemma rPropDef_wand_unseal : @rPropDef_wand = @rPropDef_wand_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Persistent connective *)

  Local Definition rPropDef_persistently_def (P: rPropDef) : rPropDef :=
    rPropDef_pure (rPropDef_entails rPropDef_empty P).

  Local Definition rPropDef_persistently_aux : seal (@rPropDef_persistently_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_persistently := unseal rPropDef_persistently_aux.
  Local Lemma rPropDef_persistently_unseal : @rPropDef_persistently = @rPropDef_persistently_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Later connective *)

  Local Definition rPropDef_later_def (P: rPropDef) : rPropDef := P.

  Local Definition rPropDef_later_aux : seal (@rPropDef_later_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_later := unseal rPropDef_later_aux.
  Local Lemma rPropDef_later_unseal : @rPropDef_later = @rPropDef_later_def.
  Proof using Type. by apply seal_eq. Qed.

End rPropDef_def.

Module rProp_primitive.
  Ltac unseal :=
    repeat (
        unfold
          equiv,
          rPropDef_equiv,
          rPropDef_pure_def,
          rPropDef_persistently_def,
          rPropDef_later_def;
        rewrite
          ?rPropDef_entails_unseal,
          ?rPropDef_pure_unseal,
          ?rPropDef_empty_unseal,
          ?rPropDef_and_unseal,
          ?rPropDef_or_unseal,
          ?rPropDef_impl_unseal,
          ?rPropDef_forall_unseal,
          ?rPropDef_exist_unseal,
          ?rPropDef_sep_unseal,
          ?rPropDef_wand_unseal,
          ?rPropDef_persistently_unseal,
          ?rPropDef_later_unseal
      ).

Section laws.
  Implicit Types φ : Prop.
  Implicit Types P Q : rPropDef.
  Implicit Types A : Type.

  Notation "P ⊢ Q" := (@rPropDef_entails P%I Q%I) : stdpp_scope.
  Notation "(⊢)" := (@rPropDef_entails) (only parsing) : stdpp_scope.
  Notation "P ⊣⊢ Q" := (@rPropDef_equiv P%I Q%I) : stdpp_scope.
  Notation "(⊣⊢)" := (@rPropDef_equiv) (only parsing) : stdpp_scope.

  Notation "'⌜' φ '⌝'" := (rPropDef_pure φ%type%stdpp)%I : bi_scope.
  Notation "'True'" := ⌜ True ⌝%I : bi_scope.
  Notation "'False'" := ⌜ False ⌝%I : bi_scope.
  Infix "∧" := rPropDef_and : bi_scope.
  Infix "∨" := rPropDef_or : bi_scope.
  Infix "→" := rPropDef_impl : bi_scope.
  Notation "∀ x .. y , P" :=
    (rPropDef_forall _ (λ x, .. (rPropDef_forall _ (λ y, P)) ..)) : bi_scope.
  Notation "∃ x .. y , P" :=
    (rPropDef_exist _ (λ x, .. (rPropDef_exist _ (λ y, P)) ..)) : bi_scope.
  Infix "∗" := rPropDef_sep : bi_scope.
  Infix "-∗" := rPropDef_wand : bi_scope.
  Notation "□ P" := (rPropDef_persistently P) : bi_scope.
  Notation "▷ P" := (rPropDef_later P) : bi_scope.
  Notation "'emp'" := (rPropDef_empty) : bi_scope.

  (** * Properties *)

  (** ** Entailement properties *)

  Instance equiv_equiv : Equivalence (⊣⊢).
  Proof using Type. unseal; constructor; now firstorder. Qed.

  Instance entails_po : PreOrder (⊢).
  Proof using Type. unseal; constructor; now firstorder. Qed.

  Lemma entails_anti_sym P Q : AntiSymm (⊣⊢) (⊢).
  Proof using Type. unseal; now firstorder. Qed.

  Lemma equiv_entails P Q : (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
  Proof. by unseal. Qed.

  (** ** Pure lifting Properties *)

  Lemma pure_ne : Proper ((↔) ==> (⊣⊢)) rPropDef_pure.
  Proof using Type.
    unseal.
    intros P P' HP. split; intros mt ms; repeat split; by apply HP.
  Qed.

  Lemma pure_intro Φ P : Φ -> P ⊢ ⌜Φ⌝.
  Proof using Type.
    unseal. intros H mt ms HP. by apply H.
  Qed.

  Lemma pure_elim Φ P :
    (Φ -> ⌜True⌝ ⊢ P) -> ⌜Φ⌝ ⊢ P.
  Proof using Type.
    unseal. intros H mt ms HΦ. by apply H.
  Qed.

  (** ** Logical Connectives *)

  (** *** And *)

  Lemma and_ne : Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) rPropDef_and.
  Proof using Type.
    unseal.
    intros P P' [HP HP'] Q Q' [HQ HQ']. split;
      intros mt ms []; split; by auto.
  Qed.

  Lemma and_intro P Q R :
    (P ⊢ Q) ->
    (P ⊢ R) ->
    P ⊢ Q ∧ R.
  Proof using Type.
    unseal.
    intros HPQ HPR mt ms HP.
    split.
    - by apply HPQ.
    - by apply HPR.
  Qed.

  Lemma and_elim_l P Q : P ∧ Q ⊢ P.
  Proof using Type.
    unseal. by intros mt ms [].
  Qed.

  Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
  Proof using Type.
    unseal. by intros mt ms [].
  Qed.

  (** *** Or *)

  Lemma or_ne : Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) rPropDef_or.
  Proof using Type.
    unseal.
    intros P P' [HP HP'] Q Q' [HQ HQ']. split;
      intros mt ms []; (left ; by auto) || (right; by auto).
  Qed.

  Lemma or_intro_l P Q : P ⊢ P ∨ Q.
  Proof using Type.
    unseal. intros mt ms HP. by left.
  Qed.

  Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
  Proof using Type.
    unseal. intros mt ms HP. by right.
  Qed.

  Lemma or_elim P Q R :
    (P ⊢ R) ->
    (Q ⊢ R) ->
    P ∨ Q ⊢ R.
  Proof using Type.
    unseal.
    intros HPR HQR mt ms [HP | HQ]; by auto.
  Qed.

  (** *** Implication *)

  Lemma impl_ne : Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) rPropDef_impl.
  Proof using Type.
    unseal.
    intros P P' [HP HP'] Q Q' [HQ HQ']. split;
      intros mt ms HPQ H; by auto.
  Qed.

  Lemma impl_intro P Q R :
    (P ∧ Q ⊢ R) ->
    P ⊢ Q → R.
  Proof using Type.
    unseal.
    intros H mt ms HP HQ. apply H. by split.
  Qed.

  Lemma impl_elim P Q R :
    (P ⊢ Q → R) ->
    P ∧ Q ⊢ R.
  Proof using Type.
    unseal.
    intros H mt ms [HP HQ]. by apply H.
  Qed.

  (** *** Forall *)

  Lemma forall_ne A :
    Proper (pointwise_relation A (⊣⊢) ==> (⊣⊢)) (rPropDef_forall A).
  Proof using Type.
    unseal.
    intros x y H. split; intros mt ms HA a; by apply H.
  Qed.

  Lemma forall_intro A P (Ψ: A -> rPropDef) :
    (∀ a, (P ⊢ Ψ a)) ->
    P ⊢ (∀ a, Ψ a).
  Proof using Type.
    unseal.
    intros H mt ms HP a. by apply H.
  Qed.

  Lemma forall_elim A (Ψ: A -> rPropDef) a :
    (∀a, Ψ a) ⊢ Ψ a.
  Proof using Type.
    unseal.
    intros mt ms H. apply H.
  Qed.

  (** *** Exist *)

  Lemma exist_ne A :
    Proper (pointwise_relation A (⊣⊢) ==> (⊣⊢)) (rPropDef_exist A).
  Proof using Type.
    unseal.
    intros x y H. split; intros mt ms []; eexists; by apply H.
  Qed.

  Lemma exist_intro A (Ψ: A -> rPropDef) a :
    (Ψ a) ⊢ ∃ a, Ψ a.
  Proof using Type.
    unseal.
    intros mt ms H. eexists. by apply H.
  Qed.

  Lemma exist_elim A (Ψ: A -> rPropDef) P :
    (∀ a, (Ψ a) ⊢ P) ->
    (∃ a, Ψ a) ⊢ P.
  Proof using Type.
    unseal.
    intros H mt ms []. by eapply H.
  Qed.

  (** *** Separating conjunction *)

  Lemma sep_ne : Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) rPropDef_sep.
  Proof using Type.
    unseal.
    intros P P' [HP HP'] Q Q' [HQ HQ'].
    split; intros ? ? (mtP & msP & mtQ & msQ & Ht & Hs & <- & <- & ? & ?);
    exists mtP, msP, mtQ, msQ; split_and!; by auto.
  Qed.

  Lemma sep_mono P P' Q Q' :
    (P ⊢ Q) ->
    (P' ⊢ Q') ->
    P ∗ P' ⊢ Q ∗ Q'.
  Proof using Type.
    unseal.
    intros H1 H2 ? ? (mtP & msP & mtQ & msQ & Ht & Hs & <- & <- & ? & ?).
    exists mtP, msP, mtQ, msQ; split_and!; by auto.
  Qed.

  Lemma emp_sep_1 P :
    P ⊢ emp ∗ P.
  Proof using Type.
    unseal.
    intros mt ms HP.
    exists ∅, ∅, mt, ms; split_and!.
    - apply map_disjoint_empty_l.
    - apply map_disjoint_empty_l.
    - apply map_empty_union.
    - apply map_empty_union.
    - by split.
    - assumption.
  Qed.

  Lemma emp_sep_2 P :
    emp ∗ P ⊢ P.
  Proof using Type.
    unseal.
    intros ? ? (? & ? & mtP & msP & Ht & Hs & <- & <- & [-> ->] & Hp).
    by rewrite !map_empty_union.
  Qed.

  Lemma sep_comm P Q :
    P ∗ Q ⊢ Q ∗ P.
  Proof using Type.
    unseal.
    intros ? ? (mtP & msP & mtQ & msQ & Ht & Hs & <- & <- & Hp & Hq).
    exists mtQ, msQ, mtP, msP. split_and!.
    - done.
    - done.
    - by apply map_union_comm.
    - by apply map_union_comm.
    - assumption.
    - assumption.
  Qed.

  Lemma sep_assoc P Q R :
    (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
  Proof using Type.
    unseal.
    intros mt ms HPQR.
    destruct HPQR as (mtPQ & msPQ & mtR & msR & Ht & Hs & <- & <- & HPQ & HR).
    destruct HPQ as (mtP & msP & mtQ & msQ & ? & ? & <- & <- & HP & HQ).
    apply map_disjoint_union_l in Ht as [], Hs as [].
    rewrite <-!map_union_assoc.
    exists mtP, msP, (mtQ ∪ mtR), (msQ ∪ msR).
    split_and!.
    - by apply map_disjoint_union_r.
    - by apply map_disjoint_union_r.
    - done.
    - done.
    - done.
    - exists mtQ, msQ, mtR, msR. by split_and!.
  Qed.

  (** *** Separating implication *)

  Lemma wand_ne : Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) rPropDef_wand.
  Proof using Type.
    unseal.
    intros P P' [HP HP'] Q Q' [HQ HQ'].
    split; intros mt ms H mtP msP Ht Hs ?.
    - by apply HQ, H, HP'.
    - by apply HQ', H, HP.
  Qed.

  Lemma wand_intro P Q R :
    (P ∗ Q ⊢ R) ->
    P ⊢ Q -∗ R.
  Proof using Type.
    unseal.
    intros H mt ms HP mtQ msQ Ht Hs HQ. apply H.
    exists mt, ms, mtQ, msQ. by split_and!.
  Qed.

  Lemma wand_elim P Q R :
    (P ⊢ Q -∗ R) ->
    P ∗ Q ⊢ R.
  Proof using Type.
    unseal.
    intros H mt ms (mtP & msP & mtQ & msQ & Ht & Hs & <- & <- & Hp & Hq).
    by apply H.
  Qed.

End laws.
End rProp_primitive.
