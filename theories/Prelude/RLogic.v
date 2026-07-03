From stdpp Require Import prelude.
From stdpp Require Import tactics.

From RSL Require Import Algebras.RA.
From RSL Require Import Algebras.Updates.

From iris.bi Require Import notation.
From Coinduction Require Import all.

#[local] Obligation Tactic := idtac.

(** * Logic Definition *)
Record rProp (M : ura) : Type := RProp {
  rProp_holds : M -> Prop;
  rProp_mono m1 m2 : rProp_holds m1 -> m1 ≼ m2 -> rProp_holds m2
}.

Local Coercion rProp_holds : rProp >-> Funclass.
Arguments rProp_holds {_} _.

(** ** Equivalence *)

Instance rProp_equiv {M} : Equiv (rProp M) :=
  fun P Q => ∀ m, ✓ m -> P m <-> Q m.

Instance rProp_equiv_equiv {M}: Equivalence (≡@{rProp M}).
Proof using Type. constructor; now firstorder. Qed.

(** ** Entailment *)

Local Definition rProp_entails_def {M} (P Q : rProp M) : Prop :=
  ∀ m, ✓ m -> rProp_holds P m -> rProp_holds Q m.

Local Definition rProp_entails_aux : seal (@rProp_entails_def).
Proof using Type. by eexists. Qed.
Definition rProp_entails := unseal rProp_entails_aux.
Local Lemma rProp_entails_unseal : @rProp_entails = @rProp_entails_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_entails {M}.

(** ** Pure lifting *)

Local Program Definition rProp_pure_def {M} (P: Prop) : rProp M :=
  {| rProp_holds _ := P |}.
Solve Obligations with easy.

Local Definition rProp_pure_aux : seal (@rProp_pure_def).
Proof using Type. by eexists. Qed.
Definition rProp_pure := unseal rProp_pure_aux.
Local Lemma rProp_pure_unseal : @rProp_pure = @rProp_pure_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_pure {M}.

(** ** Empty *)

Local Definition rProp_empty_def {M} : rProp M := rProp_pure True.

Local Definition rProp_empty_aux : seal (@rProp_empty_def).
Proof using Type. by eexists. Qed.
Definition rProp_empty := unseal rProp_empty_aux.
Local Lemma rProp_empty_unseal : @rProp_empty = @rProp_empty_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_empty {M}.

(** ** Logical Connectives *)

(** *** And *)

Local Program Definition rProp_and_def {M} (P Q: rProp M) : rProp M :=
  {| rProp_holds m := P m ∧ Q m |}.
Next Obligation.
  intros M P Q m1 m2 [HP HQ] Hle. split; by eapply rProp_mono.
Qed.

Local Definition rProp_and_aux : seal (@rProp_and_def).
Proof using Type. by eexists. Qed.
Definition rProp_and := unseal rProp_and_aux.
Local Lemma rProp_and_unseal : @rProp_and = @rProp_and_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_and {M}.

(** *** Or *)

Local Program Definition rProp_or_def {M} (P Q: rProp M) : rProp M :=
  {| rProp_holds m := P m ∨ Q m |}.
Next Obligation.
  intros M P Q m1 m2 [HP | HQ] Hle; [left | right]; by eapply rProp_mono.
Qed.

Local Definition rProp_or_aux : seal (@rProp_or_def).
Proof using Type. by eexists. Qed.
Definition rProp_or := unseal rProp_or_aux.
Local Lemma rProp_or_unseal : @rProp_or = @rProp_or_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_or {M}.

(** *** Implication *)

Local Program Definition rProp_impl_def {M} (P Q: rProp M) : rProp M :=
  {| rProp_holds m := ∀ m', m ≼ m' -> ✓ m' -> P m' -> Q m' |}.
Next Obligation.
  intros M P Q m1 m2 H Hle m' Hle'. apply H; auto. by etransitivity.
Qed.

Local Definition rProp_impl_aux : seal (@rProp_impl_def).
Proof using Type. by eexists. Qed.
Definition rProp_impl := unseal rProp_impl_aux.
Local Lemma rProp_impl_unseal : @rProp_impl = @rProp_impl_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_impl {M}.

(** *** Forall *)

Local Program Definition rProp_forall_def {M} : ∀ X (f: X -> rProp M), rProp M :=
  fun X f => {| rProp_holds m := ∀ x, f x m |}.
Next Obligation.
  intros M X f m1 m2 H Hle x. by eapply rProp_mono.
Qed.

Local Definition rProp_forall_aux : seal (@rProp_forall_def).
Proof using Type. by eexists. Qed.
Definition rProp_forall := unseal rProp_forall_aux.
Local Lemma rProp_forall_unseal : @rProp_forall = @rProp_forall_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_forall {M _}.

(** *** Exist *)

Local Program Definition rProp_exist_def {M} : ∀ X (f: X -> rProp M), rProp M :=
  fun X f => {| rProp_holds m := ∃ x, f x m |}.
Next Obligation.
  intros M X f m1 m2 [x H] Hle. exists x. by eapply rProp_mono.
Qed.

Local Definition rProp_exist_aux : seal (@rProp_exist_def).
Proof using Type. by eexists. Qed.
Definition rProp_exist := unseal rProp_exist_aux.
Local Lemma rProp_exist_unseal : @rProp_exist = @rProp_exist_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_exist {M _}.

(** *** Separating conjunction *)

Local Program Definition rProp_sep_def {M} (P Q: rProp M) : rProp M :=
  {| rProp_holds m := ∃ m1 m2, m = m1 ⋅ m2 ∧ P m1 ∧ Q m2 |}.
Next Obligation.
  intros M P Q m1 m2 (mP & mQ & -> & HP & HQ) [z Hz].
  eexists mP, (mQ ⋅ z); repeat split; eauto.
  - by rewrite ra_assoc.
  - eapply rProp_mono; eauto. apply ra_included_l.
Qed.

Local Definition rProp_sep_aux : seal (@rProp_sep_def).
Proof using Type. by eexists. Qed.
Definition rProp_sep := unseal rProp_sep_aux.
Local Lemma rProp_sep_unseal : @rProp_sep = @rProp_sep_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_sep {M}.

(** *** Separating implication *)

Local Program Definition rProp_wand_def {M} (P Q: rProp M) : rProp M :=
  {| rProp_holds m := ∀ m', ✓ (m ⋅ m') -> P m' -> Q (m ⋅ m') |}.
Next Obligation.
  simpl. intros M P Q m1 m2 H Hle m' Hv HP.
  apply rProp_mono with (m1 := m1 ⋅ m');
    eauto using ra_valid_included, ra_mono_r.
Qed.

Local Definition rProp_wand_aux : seal (@rProp_wand_def).
Proof using Type. by eexists. Qed.
Definition rProp_wand := unseal rProp_wand_aux.
Local Lemma rProp_wand_unseal : @rProp_wand = @rProp_wand_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_wand {M}.

(** *** Persistent connective *)

Local Program Definition rProp_persistently_def {M} (P: rProp M) : rProp M :=
  {| rProp_holds m := P (core m) |}.
Next Obligation.
  simpl. intros M P m1 m2 H Hle.
  eapply rProp_mono; eauto. by apply ra_core_mono.
Qed.

Local Definition rProp_persistently_aux : seal (@rProp_persistently_def).
Proof using Type. by eexists. Qed.
Definition rProp_persistently := unseal rProp_persistently_aux.
Local Lemma rProp_persistently_unseal : @rProp_persistently = @rProp_persistently_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_persistently {M}.

(** *** Later connective *)

Local Definition rProp_later_def {M} (P: rProp M) : rProp M := P.

Local Definition rProp_later_aux : seal (@rProp_later_def).
Proof using Type. by eexists. Qed.
Definition rProp_later := unseal rProp_later_aux.
Local Lemma rProp_later_unseal : @rProp_later = @rProp_later_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_later {M}.

(** *** Own connective  *)
Local Program Definition rProp_ownM_def {M: ura} (a : M) : rProp M :=
  {| rProp_holds m := a ≼ m |}.
Next Obligation.
  intros M a m1 m2 [y ->] [z ->].
  rewrite <-ra_assoc. apply ra_included_l.
Qed.

Local Definition rProp_ownM_aux : seal (@rProp_ownM_def).
Proof using Type. by eexists. Qed.
Definition rProp_ownM := unseal rProp_ownM_aux.
Local Lemma rProp_ownM_unseal : @rProp_ownM = @rProp_ownM_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_ownM {M}.

(** *** base update connective  *)

Local Program Definition rProp_bupd_def {M} (P : rProp M) : rProp M :=
  {| rProp_holds m := ∀ f, ✓ (m ⋅ f) -> ∃ m', ✓ (m' ⋅ f) ∧ P m' |}.
Next Obligation.
  simpl. intros M P m1 m2 H [z ->] f Hv.
  rewrite <-ra_assoc in Hv. apply H in Hv.
  destruct Hv as (m' & Hv & HP).
  exists (m' ⋅ z); split; auto.
  - by rewrite <-ra_assoc.
  - eapply rProp_mono; eauto. apply ra_included_l.
Qed.

Local Definition rProp_bupd_aux : seal (@rProp_bupd_def).
Proof using Type. by eexists. Qed.
Definition rProp_bupd := unseal rProp_bupd_aux.
Local Lemma rProp_bupd_unseal : @rProp_bupd = @rProp_bupd_def.
Proof using Type. by apply seal_eq. Qed.
Arguments rProp_bupd {M}.

(** * Properties *)

Module rProp_primitive.

Local Definition rProp_unseal :=
  (@rProp_entails_unseal,
   @rProp_empty_unseal,
   @rProp_pure_unseal,
   @rProp_and_unseal,
   @rProp_or_unseal,
   @rProp_impl_unseal,
   @rProp_forall_unseal,
   @rProp_exist_unseal,
   @rProp_sep_unseal,
   @rProp_wand_unseal,
   @rProp_persistently_unseal,
   @rProp_later_unseal,
   @rProp_ownM_unseal,
   @rProp_bupd_unseal).

Local Ltac unseal :=
  repeat (
    unfold equiv, rProp_equiv, rProp_empty_def;
    rewrite
      ?rProp_entails_unseal,
      ?rProp_empty_unseal,
      ?rProp_pure_unseal,
      ?rProp_and_unseal,
      ?rProp_or_unseal,
      ?rProp_impl_unseal,
      ?rProp_forall_unseal,
      ?rProp_exist_unseal,
      ?rProp_sep_unseal,
      ?rProp_wand_unseal,
      ?rProp_persistently_unseal,
      ?rProp_later_unseal,
      ?rProp_ownM_unseal,
      ?rProp_bupd_unseal;
      simpl).

Section primitive.
  Context {M : ura}.
  Implicit Types ϕ : Prop.
  Implicit Types P Q : rProp M.
  Implicit Types A : Type.

  (** The notations below are implicitly local due to the section, so we do not
      mind the overlap with the general BI notations. *)
  Notation "P ⊢ Q" := (@rProp_entails M P%I Q%I) : stdpp_scope.
  Notation "(⊢)" := (@rProp_entails M) (only parsing) : stdpp_scope.
  Notation "P ⊣⊢ Q" := (@rProp_equiv M P%I Q%I) : stdpp_scope.
  Notation "(⊣⊢)" := (@rProp_equiv M) (only parsing) : stdpp_scope.

  Notation "'⌜' φ '⌝'" := (rProp_pure φ%type%stdpp)%I : bi_scope.
  Notation "'True'" := ⌜ True ⌝%I : bi_scope.
  Notation "'False'" := ⌜ False ⌝%I : bi_scope.
  Infix "∧" := rProp_and : bi_scope.
  Infix "∨" := rProp_or : bi_scope.
  Infix "→" := rProp_impl : bi_scope.
  Notation "∀ x .. y , P" :=
    (rProp_forall (λ x, .. (rProp_forall (λ y, P)) ..)) : bi_scope.
  Notation "∃ x .. y , P" :=
    (rProp_exist (λ x, .. (rProp_exist (λ y, P)) ..)) : bi_scope.
  Infix "∗" := rProp_sep : bi_scope.
  Infix "-∗" := rProp_wand : bi_scope.
  Notation "□ P" := (rProp_persistently P) : bi_scope.
  Notation "▷ P" := (rProp_later P) : bi_scope.
  Notation "|==> P" := (rProp_bupd P) : bi_scope.

  Lemma entails_po : PreOrder (⊢).
  Proof using Type.
    unseal; constructor; now firstorder.
  Qed.

  Lemma entails_anti_sym : AntiSymm (⊣⊢) (⊣⊢).
  Proof using Type. unseal; now firstorder. Qed.

  Lemma equiv_entails P Q :
    (P ⊣⊢ Q) <-> (P ⊢ Q) ∧ (Q ⊢ P).
  Proof using Type.
    unseal. split.
    - by intros H; split; intros m Hv; rewrite (H _ Hv).
    - now intros [H1 H2] m Hm; split; auto.
  Qed.

  (** ** Pure lifting Properties *)

  Lemma pure_ne : Proper ((↔) ==> (≡)) (@rProp_pure M).
  Proof using Type.
    unseal; intros P Q H m Hm. split; intros; by apply H.
  Qed.

  Lemma and_ne : Proper ((≡) ==> (≡) ==> (≡)) (@rProp_and M).
  Proof using Type.
    unseal; intros P P' HP Q Q' HQ m Hm.
    split; (intros [??]; split; [by apply HP | by apply HQ]).
  Qed.

  Lemma or_ne : Proper ((≡) ==> (≡) ==> (≡)) (@rProp_or M).
  Proof using Type.
    unseal; intros P P' HP Q Q' HQ m Hm.
    split; (intros [?|?]; [left; by apply HP | right; by apply HQ]).
  Qed.

  Lemma impl_ne : Proper ((≡) ==> (≡) ==> (≡)) (@rProp_impl M).
  Proof using Type.
    unseal; intros P P' HP Q Q' HQ m Hm. split;
      intros H m' Hle Hm' HP'; simpl in *; apply HQ, H, HP;
      auto.
  Qed.

  Lemma sep_ne : Proper ((≡) ==> (≡) ==> (≡)) (@rProp_sep M).
  Proof using Type.
    unseal; intros P P' HP Q Q' HQ m Hm.
    split; intros (m1 & m2 & ? & ? & ?); subst m;
      exists m1, m2; repeat split;
      try (apply HP || apply HQ);
      now eauto using ra_valid_op_l, ra_valid_op_r.
  Qed.

  Lemma wand_ne : Proper ((≡) ==> (≡) ==> (≡)) (@rProp_wand M).
  Proof using Type.
    unseal; intros P P' HP Q Q' HQ m Hm.
    split; intros HPQ m' Hm' HP';
    apply HQ, HPQ, HP; now eauto using ra_valid_op_r.
  Qed.

  Lemma forall_ne A :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@rProp_forall M A).
  Proof using Type.
    unseal. intros ϕ ϕ' Hϕ m Hm.
    split; intros H a; by apply Hϕ, H.
  Qed.

  Lemma exist_ne A :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@rProp_exist M A).
  Proof using Type.
    unseal. intros ϕ ϕ' Hϕ m Hm.
    split; intros [a H]; exists a; by apply Hϕ, H.
  Qed.

  Lemma later_id (P : rProp M) : (▷ P)%I = P.
  Proof using Type. now unseal. Qed.

  Lemma persistently_ne : Proper ((=) ==> (≡)) (@rProp_persistently M).
  Proof using Type.
    intros P Q ->; unseal; intros m Hm.
    split; now eauto using ra_core_valid.
  Qed.

  Lemma ownM_ne : Proper ((=) ==> (≡)) (@rProp_ownM M).
  Proof using Type.
    intros a b Hab m Hm.
    unseal; split; intros [x H]; exists x.
    - now rewrite <- Hab.
    - now rewrite -> Hab.
  Qed.

  Lemma bupd_ne : Proper ((≡) ==> (≡)) (@rProp_bupd M).
  Proof using Type.
    intros P Q HPQ m Hm.
    unseal; split; intros H m' Hm'; destruct (H m' Hm') as (x & Hx & HP);
    exists x; split; auto; apply HPQ, HP;
    eauto using ra_valid_op_l.
  Qed.

  (** Introduction and elimination rules *)
  Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
  Proof using Type.
    unseal. intros HPQ HPR m Hv HP; split; auto.
  Qed.

  Lemma and_elim_l P Q : P ∧ Q ⊢ P.
  Proof using Type.
    unseal. by intros m Hv [HP HQ].
  Qed.

  Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
  Proof using Type.
    unseal. by intros m Hv [HP HQ].
  Qed.

  Lemma or_intro_l P Q : P ⊢ P ∨ Q.
  Proof using Type. unseal. intros m Hv HP. by left. Qed.

  Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
  Proof using Type. unseal. intros m Hv HP. by right. Qed.

  Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
  Proof using Type. unseal. intros HPR HQR m Hv [HP | HQ]; by auto. Qed.

  Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
  Proof using Type.
    unseal.
    intros H m Hv HP m' Hle Hm HQ.
    eapply H; eauto. split; auto. by eapply rProp_mono.
  Qed.

  Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
  Proof using Type.
    unseal.
    intros H m Hv [HP HQ].
    eapply H; by eauto.
  Qed.

  Lemma forall_intro {A} P (Ψ : A -> rProp M):
    (∀ a, P ⊢ Ψ a) -> P ⊢ ∀ a, Ψ a.
  Proof using Type. unseal. intros H m Hv HP a. by apply H. Qed.

  Lemma forall_elim A (Ψ: A -> rProp M) a :
    (∀ a, Ψ a) ⊢ Ψ a.
  Proof using Type. unseal. intros m Hv H. by apply H. Qed.

  Lemma exist_intro A (Ψ: A -> rProp M ) a :
    Ψ a ⊢ ∃ a, Ψ a.
  Proof using Type. unseal. intros m Hv H. by exists a. Qed.

  Lemma exist_elim A (Ψ: A -> rProp M) P :
    (∀ a, Ψ a ⊢ P) → (∃ a, Ψ a) ⊢ P.
  Proof using Type. unseal. intros H m Hv [a Ha]. by eapply H. Qed.

  (** BI connectives *)
  Lemma sep_mono P P' Q Q' :
    (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
  Proof using Type.
    unseal.
    intros H H' mt ms.
    intros (mP & mP' & -> & HP & HP').
    exists mP, mP'. split; auto. split.
    - apply H; auto. by eapply ra_valid_op_l.
    - apply H'; auto. by eapply ra_valid_op_r.
  Qed.

  Lemma True_sep_1 P :
    P ⊢ True ∗ P.
  Proof using Type.
    unseal.
    intros m Hv HP.
    exists ε, m. repeat split; auto.
    by rewrite ura_unit_l.
  Qed.

  Lemma True_sep_2 P :
    True ∗ P ⊢ P.
  Proof using Type.
    unseal. intros m Hv (? & mP & -> & _ & HP).
    eapply rProp_mono; eauto. apply ra_included_r.
  Qed.

  Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
  Proof using Type.
    unseal.
    intros m Hv (mP & mQ & -> & HP & HQ).
    exists mQ, mP. repeat split; auto using ra_comm.
  Qed.

  Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
  Proof using Type.
    unseal.
    intros m Hv HPQR.
    destruct HPQR as (mPQ & mR & -> & HPQ & HR).
    destruct HPQ as (mP & mQ & -> & HP & HQ).
    rewrite <- ra_assoc.
    eexists mP, _; repeat split; auto.
    exists mQ, mR; repeat split; auto.
  Qed.

  Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
  Proof using Type.
    unseal.
    intros H m Hv HP mQ HvQ HQ.
    apply H; auto.
    exists m, mQ. repeat split; easy.
  Qed.

  Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
  Proof using Type.
    unseal.
    intros H m Hv (mP & mQ & -> & HP & HQ).
    apply H; eauto using ra_valid_op_l.
  Qed.

  (** Persistently *)
  Lemma persistently_mono P Q : (P ⊢ Q) → □ P ⊢ □ Q.
  Proof using Type.
    unseal.
    intros H m Hv HP. apply H; auto. by apply ra_core_valid.
  Qed.

  Lemma persistently_elim P : □ P ⊢ P.
  Proof using Type.
    unseal.
    intros m Hv HP. eapply rProp_mono.
    - apply HP.
    - apply ra_included_core.
  Qed.

  Lemma persistently_idemp_2 P : □ P ⊢ □ □ P.
  Proof using Type.
    unseal; intros m; unfold rProp_persistently_def; simpl; intros Hv HP.
    by rewrite ra_core_idemp.
  Qed.

  Lemma persistently_forall_2 {A} (Ψ : A → rProp M) :
    (∀ a, □ Ψ a) ⊢ (□ ∀ a, Ψ a).
  Proof using Type. unseal; by intros m Hv H. Qed.

  Lemma persistently_exist_1 {A} (Ψ : A → rProp M) :
    (□ ∃ a, Ψ a) ⊢ (∃ a, □ Ψ a).
  Proof using Type. unseal; by intros m Hv H. Qed.

  Lemma persistently_and_sep_l_1 P Q : □ P ∧ Q ⊢ P ∗ Q.
  Proof using Type.
    unseal. intros m Hv [HP HQ].
    exists (core m), m. repeat split; auto.
    by rewrite ra_core_l.
  Qed.

  (** Basic update modality *)
  Lemma bupd_intro P : P ⊢ |==> P.
  Proof using Type.
    unseal. intros m Hv HP f ?.
    exists m; split; auto.
  Qed.

  Lemma bupd_mono P Q : (P ⊢ Q) → (|==> P) ⊢ |==> Q.
  Proof using Type.
    unseal. intros HPQ m Hv HP f ?.
    destruct (HP f) as (m' & ? & ?); auto.
    exists m'; split; auto.
    apply HPQ; auto. by eapply ra_valid_op_l.
  Qed.

  Lemma bupd_trans P : (|==> |==> P) ⊢ |==> P.
  Proof using Type.
    unseal. intros m Hv HP f ?. naive_solver.
  Qed.

  Lemma bupd_frame_r P R : (|==> P) ∗ R ⊢ |==> P ∗ R.
  Proof using Type.
    unseal. intros m Hv (mP & mR & -> & HP & HR) f ?.
    destruct (HP (mR ⋅ f)) as (m' & ? & ?).
    { by rewrite ra_assoc. }
    exists (m' ⋅ mR). split.
    - by rewrite <- ra_assoc.
    - by exists m', mR.
  Qed.

  (** Own *)
  Lemma ownM_op (a1 a2 : M) :
    rProp_ownM (a1 ⋅ a2) ⊣⊢ rProp_ownM a1 ∗ rProp_ownM a2.
  Proof using Type.
    unseal; intros m Hv; split.
    - intros [z ->]. exists a1, (a2 ⋅ z). repeat split.
      + by rewrite ra_assoc.
      + easy.
      + by apply ra_included_l.
    - intros (m1 & m2 & -> & [z1 ->] & [z2 ->]).
      rewrite ra_assoc, <-(ra_assoc a1 _ _), (ra_comm z1).
      rewrite <-(ra_assoc _ _ z2), <-(ra_assoc a2), ra_assoc.
      by eexists.
  Qed.

  Lemma persistently_ownM_core (a : M) :
    rProp_ownM a ⊢ □ rProp_ownM (core a).
  Proof using Type.
    unseal. intros m Hv H. simpl.
    by apply ra_core_mono.
  Qed.

  Lemma ownM_unit P :
    P ⊢ rProp_ownM ε.
  Proof using Type.
    unseal. intros m Hv H.
    exists m. by rewrite ura_unit_l.
  Qed.

  Lemma bupd_ownM_updateP x (Φ : M → Prop) :
    x ~~>: Φ ->
    rProp_ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ rProp_ownM y.
  Proof using Type.
    unseal. intros Hup m Hv [z ->] f ?.
    destruct (Hup (Some (z ⋅ f))) as (y&?&?); simpl in *.
    { by rewrite ra_assoc. }
    exists (y ⋅ z). split.
    { by rewrite <-ra_assoc. }
    exists y; eauto using ra_included_l.
  Qed.

  Lemma ownM_forall {A} (f : A → M) :
    (∀ a, rProp_ownM (f a)) ⊢ ∃ z, rProp_ownM z ∧ (∀ a, ∃ xf, ⌜z = f a ⋅ xf⌝).
  Proof using Type.
    unseal. intros m Hv. simpl. intros Hf.
    exists m. split.
    - easy.
    - intros a. destruct (Hf a) as [xf ?]; eauto.
  Qed.

  Lemma ownM_valid (a : M) : rProp_ownM a ⊢ ⌜✓ a⌝.
  Proof using Type.
    unseal. intros m Hv [a' ->].
    by eapply ra_valid_op_l.
  Qed.

  Section rPropLattice.
    Definition rProp_leq (P Q : rProp M) : Prop :=
      ∀ m, P m -> Q m.

    Definition rProp_weq (P Q : rProp M) : Prop :=
      ∀ m, P m ↔ Q m.

    Definition rProp_top : rProp M := ⌜True⌝%I.
    Definition rProp_bot: rProp M := ⌜False⌝%I.

    Definition rProp_join : rProp M -> rProp M -> rProp M := rProp_or.
    Definition rProp_meet : rProp M -> rProp M -> rProp M := rProp_and.

    Program Definition rProp_sup :
      ∀ I, (I -> Prop) -> (I -> rProp M) -> rProp M :=
      fun I Ps f =>
      {| rProp_holds m := ∃ i, Ps i ∧ f i m |}.
    Next Obligation.
      intros I P f m1 m2 [i [HPi Hf]] Hle.
      exists i; split; auto. eapply rProp_mono; eauto.
    Qed.

    Program Definition rProp_inf :
      ∀ I, (I -> Prop) -> (I -> rProp M) -> rProp M :=
      fun I Ps f =>
        {| rProp_holds m := ∀ i, Ps i -> f i m |}.
    Next Obligation.
      intros I P f m1 m2 Hf Hle i HPi.
      eapply rProp_mono; eauto.
    Qed.

    Instance rProp_CompleteLattice : lattice.CompleteLattice (rProp M).
    Proof using Type.
      refine {|
          lattice.weq := rProp_weq;
          lattice.leq := rProp_leq;
          lattice.sup' := rProp_sup;
          lattice.inf' := rProp_inf;
          lattice.cup := rProp_join;
          lattice.cap := rProp_meet;
          lattice.bot := rProp_bot;
          lattice.top := rProp_top
        |}.
      (* Now we prove the 8 properties of CL_props *)
      split.
      { split.
        - (* 1. PreOrder leq: Reflexivity *)
          intros x m Hxm; exact Hxm.
        - (* 2. PreOrder leq: Transitivity *)
          intros x y z Hxy Hyz m Hxm. apply Hyz, Hxy, Hxm.
      } split. {
        (* 3. weq_spec *)
        intros P Q; split; intros H.
        - split; intros m Hm; apply H; auto.
        - intros m; destruct H as [HPQ HQP]; split; intros Hm.
          + apply HPQ; auto.
          + apply HQP; auto.
      } split. {
        (* 4. sup_spec *)
        intros I P f z; split; intros H.
        - intros i HPi m Hfim. apply H. exists i; split; auto.
        - intros m [i [HPi Hfim]]. eapply H; eauto.
      } split. {
        (* 5. inf_spec *)
        intros I P f z; split; intros H.
        - intros i HPi m Hzm. apply H; auto.
        - intros m Hzm i HPi. eapply H; eauto.
      } split. {
        (* 6. cup_spec (join / or) *)
        intros P Q R; split; intros H.
        - split; intros m Hm; apply H; unfold rProp_join; unseal; eauto.
        - intros m. unfold rProp_join. unseal. intros Hm. destruct H as [HPR HQR].
          destruct Hm; eauto.
      } split. {
        (* 7. cap_spec (meet / and) *)
        intros P Q R; split; unfold rProp_meet; unseal; intros H.
        - split.
          + intros m Hm. by apply H.
          + intros m Hm. by apply H.
        - intros m Hm. destruct H as [HPR HQR].
          split.
          + by apply HPR.
          + by apply HQR.
      } split. {
        (* 8. leq_bx (bot) *)
        intros P m. unfold rProp_bot. by unseal.
      } {
        (* 9. leq_xt (top) *)
        intros P m HP. unfold rProp_top. by unseal.
      }
    Defined.

    Lemma rProp_coinduction {T: Type} (b: lattice.mon (T -> rProp M)) (P: T -> rProp M):
      (∀ C: tower.Chain b,
         (∀ x, P x ⊢ tower.elem C x) ->
         ∀ x, P x ⊢ b (tower.elem C) x
      ) ->
      ∀ x, P x ⊢ tower.gfp b x.
    Proof using Type.
      unseal; unfold rProp_entails_def.
      intros RIH.
      apply tower.
      { intros F HF x m Hval HPm i HPi. apply HF; auto. }
      apply RIH.
    Qed.

    Lemma rProp_pure_coinduction {T: Type} (b: mon (T -> Prop)) (P: T -> rProp M):
      (∀ C: Chain b,
         (∀ x, P x ⊢ ⌜elem C x⌝) ->
         ∀ x, P x ⊢ ⌜b (elem C) x⌝
      ) ->
      ∀ x, P x ⊢ ⌜gfp b x⌝.
    Proof using Type.
      unseal; unfold rProp_entails_def, rProp_pure_def. simpl.
      intros RIH.
      coinduction R CIH.
      apply RIH, CIH.
    Qed.

    End rPropLattice.
End primitive.
End rProp_primitive.
