From RSL Require Import Prelude.

From RSL.Logic Require Export rPropDef.

From iris.bi Require Import notation.

Module rProp_primitive.
Import Tactic.

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
  Proof using Type. unseal. constructor; by firstorder. Qed.

  Instance entails_po : PreOrder (⊢).
  Proof using Type. unseal; constructor; now firstorder. Qed.

  Lemma entails_anti_sym P Q : AntiSymm (⊣⊢) (⊢).
  Proof using Type. unseal; now firstorder. Qed.

  Lemma equiv_entails P Q : (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
  Proof using Type. by unseal. Qed.

  (** ** Pure lifting Properties *)

  Lemma pure_ne : Proper ((↔) ==> (⊣⊢)) rPropDef_pure.
  Proof using Type.
    unseal.
    intros P P' HP. split; intros mt ms; repeat split; by apply HP.
  Qed.

  Lemma pure_intro Φ P : Φ -> P ⊢ ⌜Φ⌝.
  Proof using Type.
    unseal.
    intros H mt ms HP. by apply H.
  Qed.

  Lemma pure_elim Φ P :
    (Φ -> ⌜True⌝ ⊢ P) -> ⌜Φ⌝ ⊢ P.
  Proof using Type.
    unseal.
    intros H mt ms HΦ. by apply H.
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
    intros H mt ms [HP HQ]. by eapply H.
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
    split; intros mt ms (mtP & msP & mtQ & msQ & Ht & Hs & <- & <- & ? & ?);
    exists mtP, msP, mtQ, msQ; split_and!; by auto.
  Qed.

  Lemma sep_mono P P' Q Q' :
    (P ⊢ Q) ->
    (P' ⊢ Q') ->
    P ∗ P' ⊢ Q ∗ Q'.
  Proof using Type.
    unseal.
    intros H1 H2 mt ms (mtP & msP & mtQ & msQ & Ht & Hs & <- & <- & ? & ?).
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
    - reflexivity.
    - reflexivity.
    - assumption.
  Qed.

  Lemma emp_sep_2 P :
    emp ∗ P ⊢ P.
  Proof using Type.
    unseal.
    intros mt ms (? & ? & mtP & msP & Ht & Hs & <- & <- & [-> ->] & Hp).
    by rewrite !map_empty_union.
  Qed.

  Lemma sep_comm P Q :
    P ∗ Q ⊢ Q ∗ P.
  Proof using Type.
    unseal.
    intros mt ms (mtP & msP & mtQ & msQ & Ht & Hs & <- & <- & Hp & Hq).
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
    split; intros mt ms H mtP msP Ht Hs Hprop.
    - by apply HQ, H, HP'.
    - by apply HQ', H, HP.
  Qed.

  Lemma wand_intro P Q R :
    (P ∗ Q ⊢ R) ->
    P ⊢ Q -∗ R.
  Proof using Type.
    unseal.
    intros H mt ms HP mtQ msQ Ht Hs HQ. eapply H.
    exists mt, ms, mtQ, msQ. split_and!; by auto.
  Qed.

  Lemma wand_elim P Q R :
    (P ⊢ Q -∗ R) ->
    P ∗ Q ⊢ R.
  Proof using Type.
    unseal.
    intros H mt ms (mtP & msP & mtQ & msQ & Ht & Hs & <- & <- & Hp & Hq).
    by eapply H.
  Qed.


  Lemma later_ne : Proper ((⊣⊢) ==> (⊣⊢)) rPropDef_later.
  Proof using Type.
    unseal. intros P P' [HP HP'].
    split; intros mt ms H.
    - by apply HP, H.
    - by apply HP', H.
  Qed.

  Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
  Proof using Type.
    unseal.
    intros H mt ms HP.
    by apply H, HP.
  Qed.

  Lemma later_intro P : P ⊢ ▷ P.
  Proof using Type.
    unseal. by intros mt ms HP.
  Qed.

  Lemma later_forall_2 {A} (Φ : A -> rPropDef) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
  Proof using Type.
    unseal.
    intros mt ms H a. by apply H.
  Qed.

  Lemma later_exist_false {A} (Φ : A -> rPropDef) :
    (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
  Proof using Type.
    unseal.
    intros mt ms H. by right.
  Qed.

  Lemma later_sep_1 P Q : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q.
  Proof using Type.
    unseal. intros mt ms H.
    destruct H as (mtP & msP & mtQ & msQ & Ht & Hs & <- & <- & HP & HQ).
    exists mtP, msP, mtQ, msQ.
    by split_and!; auto.
  Qed.

  Lemma later_sep_2 P Q : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q).
  Proof using Type.
    unseal.
    intros mt ms (mtP & msP & mtQ & msQ & Ht & Hs & <- & <- & HP & HQ).
    exists mtP, msP, mtQ, msQ. by split_and!; auto.
  Qed.

  Lemma later_persistently_1 P : ▷ □ P ⊢ □ ▷ P.
  Proof using Type.
    unseal.
    intros mt ms H. by apply H.
  Qed.

  Lemma later_persistently_2 P : □ ▷ P ⊢ ▷ □ P.
  Proof using Type.
    unseal.
    intros mt ms H. by apply H.
  Qed.

  Lemma later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
  Proof using Type.
    unseal.
    intros mt ms H.
    right. intros _. apply H.
  Qed.

  Lemma persistently_ne : Proper ((⊣⊢) ==> (⊣⊢)) rPropDef_persistently.
  Proof using Type.
    unseal.
    intros P P' [HP HP']. split; intros mt ms H.
    - by apply HP.
    - by apply HP'.
  Qed.

  Lemma persistently_mono P Q : (P ⊢ Q) -> □ P ⊢ □ Q.
  Proof using Type.
    unseal.
    intros H mt ms HP.
    by apply H.
  Qed.

  Lemma persistently_idemp_2 P : □ P ⊢ □ □ P.
  Proof using Type.
    unseal.
    intros mt ms HP.
    exact HP.
  Qed.

  Lemma persistently_emp_2 : emp ⊢ □ emp.
  Proof using Type.
    unseal.
    intros mt ms Hemp.
    by split.
  Qed.

  Lemma persistently_and_2 P Q : (□ P) ∧ (□ Q) ⊢ □ (P ∧ Q).
  Proof using Type.
    unseal.
    intros mt ms [HP HQ].
    by split.
  Qed.

  Lemma persistently_absorbing P Q : □ P ∗ Q ⊢ □ P.
  Proof using Type.
    unseal.
    intros mt ms (mtP & msP & mtQ & msQ & Ht & Hs & Hmt & Hms & HP & HQ).
    exact HP.
  Qed.

  Lemma persistently_and_sep_elim P Q : □ P ∧ Q ⊢ P ∗ Q.
  Proof using Type.
    unseal.
    intros mt ms [HP HQ].
    exists ∅, ∅, mt, ms. split_and!.
    - apply map_disjoint_empty_l.
    - apply map_disjoint_empty_l.
    - apply map_empty_union.
    - apply map_empty_union.
    - exact HP.
    - exact HQ.
  Qed.

  Lemma persistently_forall_2 {A} (Ψ : A -> rPropDef) :
    (∀ a, □ (Ψ a)) ⊢ □ (∀ a, Ψ a).
  Proof using Type.
    unseal.
    intros mt ms H. by apply H.
  Qed.
  Lemma persistently_exist_1 {A} (Ψ : A -> rPropDef) :
    □ (∃ a, Ψ a) ⊢ ∃ a, □ Ψ a.
  Proof using Type.
    unseal.
    intros mt ms H. by apply H.
  Qed.

  Lemma pure_forall_2 {A} (φ : A -> Prop) :
    (∀ a, ⌜ φ a ⌝) ⊢ ⌜ ∀ a, φ a ⌝.
  Proof using Type.
    unseal.
    intros mt ms H. by apply H.
  Qed.

End laws.
End rProp_primitive.
