From RSL Require Import Prelude.

Class PCore (A : Type) := pcore : A -> option A.
Global Hint Mode PCore ! : typeclass_instances.

Class Op (A : Type) := op : A -> A -> A.
Global Hint Mode Op ! : typeclass_instances.
Infix "⋅" := op (at level 50, left associativity) : stdpp_scope.
Notation "(⋅)" := op (only parsing) : stdpp_scope.

Definition opM `{!Op A} (x : A) (my : option A) :=
  match my with Some y => x ⋅ y | None => x end.
Infix "⋅?" := opM (at level 50, left associativity) : stdpp_scope.

Class Valid (A : Type) := valid : A -> Prop.
Global Hint Mode Valid ! : typeclass_instances.
Notation "✓ x" := (valid x) (at level 20, right associativity) : stdpp_scope.

Definition included {A} `{Op A} (x y : A) := ∃ z, y = x ⋅ z.
Infix "≼" := included (at level 70) : stdpp_scope.

Class Unit (A : Type) := ε : A.
Global Hint Mode Unit ! : typeclass_instances.
Global Arguments ε {_ _}.

Record RaMixin A `{PCore A} `{Op A} `{Valid A} `{EqDecision A} := {
    (* RA-ASSOC: ∀ a b c. a · (b · c) = (a · b) · c *)
    mixin_ra_assoc : ∀ x y z : A, x ⋅ (y ⋅ z) = (x ⋅ y) ⋅ z;

    (* RA-COMM: ∀ a b. a · b = b · a *)
    mixin_ra_comm : ∀ x y : A, x ⋅ y = y ⋅ x;

    (* RA-CORE-ID: ∀ a. |a| ∈ M ⇒ |a| · a = a *)
    mixin_ra_pcore_l : ∀ (x cx : A), pcore x = Some cx -> cx ⋅ x = x;

    (* RA-CORE-IDEM: ∀ a. |a| ∈ M => ||a|| = |a| *)
    mixin_ra_pcore_idemp : ∀ (x cx : A), pcore x = Some cx -> pcore cx = Some cx;

    (* RA-CORE-MONO: ∀ a b. |a| ∈ M ∧ a ≼ b => |b| ∈ M ∧ |a| ≼ |b| *)
    mixin_ra_pcore_mono : ∀ (x y cx : A),
      x ≼ y -> pcore x = Some cx -> ∃ cy, pcore y = Some cy ∧ cx ≼ cy;

    (* RA-VALID-OP: ∀ a b. V(a · b) => V(a) *)
    mixin_ra_valid_op_l : ∀ x y : A, ✓ (x ⋅ y) -> ✓ x
  }.

Structure ra := Ra
  {
    ra_car :> Type;
    ra_pcore : PCore ra_car;
    ra_op : Op ra_car;
    ra_valid : Valid ra_car;
    ra_eq_dec : EqDecision ra_car;
    ra_mixin : RaMixin ra_car
  }.


Global Arguments Ra _ {_ _ _ _} _.

Global Hint Extern 0 (PCore _) => refine (ra_pcore _); shelve : typeclass_instances.
Global Hint Extern 0 (Op _) => refine (ra_op _); shelve : typeclass_instances.
Global Hint Extern 0 (Valid _) => refine (ra_valid _); shelve : typeclass_instances.

Global Existing Instance ra_eq_dec.

Definition ra_mixin_of' A {Ac : ra} (f : Ac → A) : RaMixin Ac := ra_mixin Ac.

Abbreviation ra_mixin_of A :=
  ltac:(let H := eval hnf in (ra_mixin_of' A id) in exact H) (only parsing).

(** Lifting properties from the mixin *)
Section ra_mixin.
  Context {A : ra}.
  Implicit Types x y : A.

  Lemma ra_assoc x y z : x ⋅ (y ⋅ z) = (x ⋅ y) ⋅ z.
  Proof using Type. by apply (mixin_ra_assoc _ (ra_mixin A)). Qed.

  Lemma ra_comm x y : x ⋅ y = y ⋅ x.
  Proof using Type. by apply (mixin_ra_comm _ (ra_mixin A)). Qed.

  Lemma ra_pcore_l x cx : pcore x = Some cx -> cx ⋅ x = x.
  Proof using Type. by apply (mixin_ra_pcore_l _ (ra_mixin A)). Qed.

  Lemma ra_pcore_idemp x cx : pcore x = Some cx -> pcore cx = Some cx.
  Proof using Type. by apply (mixin_ra_pcore_idemp _ (ra_mixin A)). Qed.

  Lemma ra_pcore_mono x y cx :
    x ≼ y ->
    pcore x = Some cx ->
    ∃ cy, pcore y = Some cy ∧ cx ≼ cy.
  Proof using Type. by apply (mixin_ra_pcore_mono _ (ra_mixin A)). Qed.

  Lemma ra_valid_op_l x y : ✓ (x ⋅ y) -> ✓ x.
  Proof using Type. by apply (mixin_ra_valid_op_l _ (ra_mixin A)). Qed.

  Lemma ra_valid_op_r x y : ✓ (x ⋅ y) -> ✓ y.
  Proof using Type.
    intros H. rewrite ra_comm in H. by apply (ra_valid_op_l _ x).
  Qed.
End ra_mixin.

(** ** CoreId elements *)
Class CoreId {A : ra} (x : A) :=
  core_id : pcore x = Some x.
Global Arguments core_id {_} _ {_}.
Global Hint Mode CoreId + ! : typeclass_instances.

(** ** Exclusive elements (i.e., elements that cannot have a frame). *)
Class Exclusive {A : ra} (x : A) :=
  exclusive_l y : ✓ (x ⋅ y) -> False.
Global Arguments exclusive_l {_} _ {_} _ _.
Global Hint Mode Exclusive + ! : typeclass_instances.

(** ** Cancelable elements. *)
Class Cancelable {A : ra} (x : A) :=
  cancelable y z : ✓ (x ⋅ y) -> x ⋅ y = x ⋅ z -> y = z.
Global Arguments cancelable {_} _ {_} _ _ _ _.
Global Hint Mode Cancelable + ! : typeclass_instances.

(** ** Identity-free elements. *)
Class IdFree {A : ra} (x : A) :=
  id_free_r y : ✓ x -> x ⋅ y = x -> False.
Global Arguments id_free_r {_} _ {_} _ _ _.
Global Hint Mode IdFree + ! : typeclass_instances.

Class RaTotal (A : ra) := ra_total (x : A) : is_Some (pcore x).
Global Arguments ra_total {_ _} _.
Global Hint Mode RaTotal ! : typeclass_instances.

Definition core {A} `{PCore A} (x : A) : A := default x (pcore x).

Section ra_prop.
  Context {A : ra}.
  Implicit Types x y z : A.

  Lemma ra_op_opM_assoc x y mz : (x ⋅ y) ⋅? mz = x ⋅ (y ⋅? mz).
  Proof using Type. destruct mz; simpl; by rewrite <- ?ra_assoc. Qed.

  (** ** Core *)
  Lemma ra_pcore_l' x cx : pcore x = Some cx -> cx ⋅ x = x.
  Proof using Type.
    intros H. by apply ra_pcore_l.
  Qed.

  Lemma ra_pcore_r x cx : pcore x = Some cx -> x ⋅ cx = x.
  Proof using Type.
    intros. rewrite ra_comm. by apply ra_pcore_l.
  Qed.

  Lemma ra_pcore_r' x cx : pcore x = Some cx -> x ⋅ cx = x.
  Proof using Type.
    intros H. by apply ra_pcore_r.
  Qed.

  Lemma ra_pcore_idemp' x cx : pcore x = Some cx -> pcore cx = Some cx.
  Proof using Type.
    intros H. eauto using ra_pcore_idemp.
  Qed.

  Lemma ra_pcore_dup x cx : pcore x = Some cx -> cx = cx ⋅ cx.
  Proof using Type.
    intros; symmetry; eauto using ra_pcore_r', ra_pcore_idemp.
  Qed.

  Lemma ra_pcore_dup' x cx : pcore x = Some cx -> cx = cx ⋅ cx.
  Proof using Type.
    intros; symmetry; eauto using ra_pcore_r', ra_pcore_idemp'.
  Qed.

  Lemma ra_pcore_valid x cx : ✓ x -> pcore x = Some cx -> ✓ cx.
  Proof using Type.
    intros Hv Hx%ra_pcore_l. revert Hv. rewrite <- Hx. apply ra_valid_op_l.
  Qed.

  (** ** Exclusive elements *)
  Lemma exclusive_r x `{!Exclusive x} y : ✓ (y ⋅ x) → False.
  Proof using Type. rewrite ra_comm. by apply exclusive_l. Qed.

  Lemma exclusive_opM x `{!Exclusive x} my : ✓ (x ⋅? my) → my = None.
  Proof using Type.
    destruct my as [y|]; last done. by intros H%exclusive_l.
  Qed.

  Lemma exclusive_included x `{!Exclusive x} y : x ≼ y → ✓ y → False.
  Proof using Type. intros [? ->]. by apply exclusive_l. Qed.

  (** ** Order *)
  Global Instance ra_included_trans: Transitive (@included A _).
  Proof using Type.
    intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2).
    by rewrite ra_assoc, <- Hy, <-Hz.
  Qed.

  Lemma ra_valid_included x y : ✓ y -> x ≼ y -> ✓ x.
  Proof using Type.
    intros Hyv [z ?]; setoid_subst; eauto using ra_valid_op_l.
  Qed.

  Lemma ra_included_l x y : x ≼ x ⋅ y.
  Proof using Type. by exists y. Qed.

  Lemma ra_included_r x y : y ≼ x ⋅ y.
  Proof using Type. rewrite ra_comm; apply ra_included_l. Qed.

  Lemma ra_pcore_mono' x y cx :
    x ≼ y -> pcore x = Some cx -> ∃ cy, pcore y = Some cy ∧ cx ≼ cy.
  Proof using Type.
    intros ? H.
    destruct (ra_pcore_mono x y cx) as (cy&->&?); auto.
    by exists cy.
  Qed.

  Lemma ra_included_pcore x cx : pcore x = Some cx -> cx ≼ x.
  Proof using Type. exists x. by rewrite ra_pcore_l. Qed.

  Lemma ra_mono_l x y z : x ≼ y -> z ⋅ x ≼ z ⋅ y.
  Proof using Type.
    by intros [z1 Hz1]; exists z1; rewrite Hz1, ra_assoc.
  Qed.

  Lemma ra_mono_r x y z : x ≼ y -> x ⋅ z ≼ y ⋅ z.
  Proof using Type.
    by intros; rewrite <- !(ra_comm z _); apply ra_mono_l.
  Qed.

  Lemma ra_mono x1 x2 y1 y2 : x1 ≼ y1 -> x2 ≼ y2 -> x1 ⋅ x2 ≼ y1 ⋅ y2.
  Proof using Type.
    intros; etransitivity; eauto using ra_mono_l, ra_mono_r.
  Qed.

  Global Instance ra_mono' :
    Proper (included ==> included ==> included) (@op A _).
  Proof using Type. intros x1 x2 Hx y1 y2 Hy. by apply ra_mono. Qed.

  (** ** CoreId elements *)
  Lemma core_id_dup x `{!CoreId x} : x = x ⋅ x.
  Proof using Type. by apply ra_pcore_dup' with x. Qed.

  Lemma core_id_extract x y `{!CoreId x} :
    x ≼ y -> y = y ⋅ x.
  Proof using Type.
    intros ?.
    destruct (ra_pcore_mono' x y x) as (cy & Hcy & [x' Hx']); auto.
    erewrite <-(ra_pcore_r y). 2: eassumption.
    rewrite Hx', <- !ra_assoc. f_equiv.
    by rewrite (ra_comm x' x), ra_assoc, <-core_id_dup.
  Qed.

  Global Instance cancelable_op x y :
    Cancelable x → Cancelable y → Cancelable (x ⋅ y).
  Proof using Type.
    intros ?? z z' ??. apply (cancelable y), (cancelable x).
    - eapply ra_valid_op_r. by rewrite ra_assoc.
    - by rewrite ra_assoc.
    - by rewrite !ra_assoc.
  Qed.

  Global Instance exclusive_cancelable (x : A) : Exclusive x → Cancelable x.
  Proof using Type. by intros ? z z' []%exclusive_l. Qed.

  (** Id-free elements  *)
  Lemma id_free_l x `{!IdFree x} y : ✓x → y ⋅ x = x → False.
  Proof using Type. rewrite ra_comm. eauto using id_free_r. Qed.

  Global Instance id_free_op_r x y : IdFree y → Cancelable x → IdFree (x ⋅ y).
  Proof using Type.
    intros ?? z ? Hid%symmetry. revert Hid.
    rewrite <-ra_assoc. intros ?%(cancelable x); auto.
    apply (id_free_l y z).
    - by eapply ra_valid_op_r.
    - by rewrite ra_comm.
  Qed.

  Global Instance id_free_op_l x y : IdFree x → Cancelable y → IdFree (x ⋅ y).
  Proof using Type. intros. rewrite ra_comm. apply _. Qed.

  Global Instance exclusive_id_free x : Exclusive x → IdFree x.
  Proof using Type.
    intros ? z Hv Hx. rewrite <-Hx in Hv.
    by eauto using exclusive_l.
  Qed.

  Section total_core.
    Context `{HTot: RaTotal A}.

    Lemma ra_pcore_core x : pcore x = Some (core x).
    Proof using HTot.
      unfold core. destruct (ra_total x) as [cx ->]. done.
    Qed.

    Lemma ra_core_l x : core x ⋅ x = x.
    Proof using HTot.
      unfold core.
      destruct (ra_total x) as [cx Hcx].
      rewrite !Hcx. now apply ra_pcore_l.
    Qed.

    Lemma ra_core_idemp x : core (core x) = core x.
    Proof using HTot.
      unfold core.
      destruct (ra_total x) as [cx Hcx].
      rewrite !Hcx. by erewrite ra_pcore_idemp.
    Qed.

    Lemma ra_core_mono x y : x ≼ y -> core x ≼ core y.
    Proof using HTot.
      intros; destruct (ra_total x) as [cx Hcx].
      destruct (ra_pcore_mono x y cx) as (cy & Hcy & ?); auto.
      unfold core. now rewrite Hcx, Hcy.
    Qed.

    Global Instance ra_core_proper : Proper ((=) ==> (=)) (@core A _).
    Proof using HTot.
      intros x y Hxy. destruct (ra_total x) as [cx Hcx].
      unfold core. by rewrite <- Hxy, Hcx.
    Qed.

    Lemma ra_core_r x : x ⋅ core x = x.
    Proof using HTot. rewrite ra_comm. apply ra_core_l. Qed.

    Lemma ra_core_dup x : core x = core x ⋅ core x.
    Proof using HTot.
      rewrite <- (ra_core_idemp x) at 3.
      by rewrite ra_core_r.
    Qed.

    Lemma ra_core_valid x : ✓ x -> ✓ core x.
    Proof using HTot.
      rewrite <- (ra_core_l x) at 1.
      by apply ra_valid_op_l.
    Qed.

    Lemma core_id_total x : CoreId x ↔ core x = x.
    Proof using HTot.
      split.
      - intros H. unfold core. by rewrite H.
      - unfold CoreId, core.
        destruct (ra_total x) as [? ->]. simpl. by intros ->.
    Qed.

    Lemma core_id_core x `{!CoreId x} : core x = x.
    Proof using HTot. by apply core_id_total. Qed.

    Lemma ra_pcore_core_id x y : pcore x = Some y -> CoreId y.
    Proof using HTot. unfold CoreId. eauto using ra_pcore_idemp. Qed.

    Global Instance ra_core_core_id x : CoreId (core x).
    Proof using HTot. eapply ra_pcore_core_id. by rewrite ra_pcore_core. Qed.

    Lemma ra_included_core x : core x ≼ x.
    Proof using HTot. by exists x; rewrite ra_core_l. Qed.


    Global Instance ra_included_preorder : PreOrder (@included A _).
    Proof using HTot.
      split; [|apply _]. by intros x; exists (core x); rewrite ra_core_r.
    Qed.
  End total_core.

End ra_prop.


Record URaMixin A `{PCore A, Op A, Valid A, Unit A}
  := {
    (* V(ε) *)
    mixin_ura_unit_valid : ✓ (ε : A);

    (* ∀ a ∈ M. ε · a = a *)
    mixin_ura_unit_l : ∀ x : A, ε ⋅ x = x;

    (* |ε| = ε *)
    mixin_ura_pcore_unit : pcore ε = Some (ε : A)
  }.

Structure ura := URa'
  {
    ura_car :> Type;
    ura_pcore : PCore ura_car;
    ura_op : Op ura_car;
    ura_valid : Valid ura_car;
    ura_unit : Unit ura_car;
    ura_eq_dec : EqDecision ura_car;
    ura_ra_mixin : RaMixin ura_car;
    ura_mixin : URaMixin ura_car
  }.

Global Arguments URa' _ {_ _ _ _ _} _ _.
Abbreviation URa A m := (URa' A (ra_mixin_of A%type) m) (only parsing).

Global Existing Instance ura_eq_dec.
Global Hint Extern 0 (Unit _) => refine (ura_unit _); shelve : typeclass_instances.

Coercion ura_raR (A : ura) : ra :=
  Ra A (ura_ra_mixin A).

Canonical Structure ura_raR.

(** Lifting properties from the mixin *)
Section ura_mixin.
  Context {A : ura}.
  Implicit Types x y : A.

  Lemma ura_unit_valid : ✓ (ε : A).
  Proof using Type. exact (mixin_ura_unit_valid _ (ura_mixin A)). Qed.

  Lemma ura_unit_l x : ε ⋅ x = x.
  Proof using Type. exact (mixin_ura_unit_l _ (ura_mixin A) x). Qed.

  Lemma ura_pcore_unit : pcore (ε:A) = Some ε.
  Proof using Type. exact (mixin_ura_pcore_unit _ (ura_mixin A)). Qed.
End ura_mixin.

Section ura_prop.
  Context {A : ura}.
  Implicit Types x y z : A.

  Lemma ura_unit_least x : ε ≼ x.
  Proof using Type. by exists x; rewrite ura_unit_l. Qed.

  Lemma ura_unit_r x : x ⋅ ε = x.
  Proof using Type. rewrite ra_comm. by apply ura_unit_l. Qed.

  Global Instance ura_unit_core_id : CoreId (ε:A).
  Proof using Type. by apply ura_pcore_unit. Qed.

  Global Instance ura_total : RaTotal A.
  Proof using Type.
    intros x. destruct (ra_pcore_mono' ε x ε) as (cx&->&?); [..|by eauto].
    - apply ura_unit_least.
    - apply @core_id. apply _.
  Qed.
End ura_prop.


(** * Transporting a ressource algebra equality *)
Definition ra_transport {A B : ra} (H : A = B) (x : A) : B :=
  eq_rect A id x _ H.

Lemma ra_transport_trans {A B C : ra} (H1 : A = B) (H2 : B = C) x :
  ra_transport H2 (ra_transport H1 x) = ra_transport (eq_trans H1 H2) x.
Proof. by destruct H2. Qed.

Section ra_transport.
  Context {A B : ra} (H : A = B).
  Abbreviation T := (ra_transport H).

  Lemma ra_transport_op x y : T (x ⋅ y) = T x ⋅ T y.
  Proof using Type. by destruct H. Qed.

  Lemma ra_transport_core x : T (core x) = core (T x).
  Proof using Type. by destruct H. Qed.

  Lemma ra_transport_valid x : ✓ T x ↔ ✓ x.
  Proof using Type. by destruct H. Qed.

  Global Instance ra_transport_core_id x : CoreId x → CoreId (T x).
  Proof using Type. by destruct H. Qed.
End ra_transport.

(** * Constructing a CMRA with total core *)
Section ra_total.
  Context (A: Type).
  Context `{PCore A} `{Op A} `{Valid A} `{EqDecision A}.
  Context (total : ∀ x : A, is_Some (pcore x)).
  Context (op_assoc : ∀ x y z : A, x ⋅ (y ⋅ z) = (x ⋅ y) ⋅ z).
  Context (op_comm : ∀ x y : A, x ⋅ y = y ⋅ x).
  Context (core_l : ∀ x : A, core x ⋅ x = x).
  Context (core_idemp : ∀ x : A, core (core x) = core x).
  Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y).
  Context (valid_op_l : ∀ x y : A, ✓ (x ⋅ y) → ✓ x).

  Local Lemma pcore_core (x k : A) : pcore x = Some k <-> core x = k.
  Proof using total.
    split; intros Hc.
    - unfold core. now rewrite Hc.
    - destruct (total x) as [k' Hk].
      unfold core in Hc. rewrite Hk in Hc. now inv Hc.
  Qed.

  Lemma ra_total_mixin : RaMixin A.
  Proof using Type*.
    split; auto.
    - intros x cx Hcx. rewrite pcore_core in Hcx. by subst.
    - intros x cx Hcx. rewrite pcore_core in *. by subst.
    - intros x y cx Hlt Hcx. rewrite pcore_core in Hcx.
      subst. eexists. rewrite pcore_core. split; by auto.
  Qed.
End ra_total.
