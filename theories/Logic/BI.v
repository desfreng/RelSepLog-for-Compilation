From RSL Require Import Prelude.

From iris.bi Require Export bi.
From iris.proofmode Require Export proofmode.

From RSL.Logic Require Import rPropDef rPropLaw.

Section BI_def.
  Import rProp_primitive.

  Local Instance rPropDef_dist : Dist rPropDef := fun _ => equiv.

  (** ** BI Mixin *)

  Lemma rProp_bi_mixin :
    BiMixin
      rPropDef_entails
      rPropDef_empty
      rPropDef_pure
      rPropDef_and
      rPropDef_or
      rPropDef_impl
      rPropDef_forall
      rPropDef_exist
      rPropDef_sep
      rPropDef_wand.
  Proof using Type.
    constructor.
    - by apply entails_po.
    - by apply equiv_entails.
    - unfold dist, rPropDef_dist; intros _.
      by apply pure_ne.
    - unfold dist, rPropDef_dist; intros _.
      by apply and_ne.
    - unfold dist, rPropDef_dist; intros _.
      by apply or_ne.
    - unfold dist, rPropDef_dist; intros _.
      by apply impl_ne.
    - unfold dist, rPropDef_dist; intros ? _.
      by apply forall_ne.
    - unfold dist, rPropDef_dist; intros ? _.
      by apply exist_ne.
    - unfold dist, rPropDef_dist; intros _.
      by apply sep_ne.
    - unfold dist, rPropDef_dist; intros _.
      by apply wand_ne.
    - by apply pure_intro.
    - by apply pure_elim.
    - by apply and_elim_l.
    - by apply and_elim_r.
    - by apply and_intro.
    - by apply or_intro_l.
    - by apply or_intro_r.
    - by apply or_elim.
    - by apply impl_intro.
    - by apply impl_elim.
    - by apply forall_intro.
    - by apply forall_elim.
    - by apply exist_intro.
    - by apply exist_elim.
    - by apply sep_mono.
    - by apply emp_sep_1.
    - by apply emp_sep_2.
    - by apply sep_comm.
    - by apply sep_assoc.
    - by apply wand_intro.
    - by apply wand_elim.
  Qed.


  Definition bi_later_mixin :
    BiLaterMixin
      rPropDef_entails
      rPropDef_pure
      rPropDef_or
      rPropDef_impl
      rPropDef_forall
      rPropDef_exist
      rPropDef_sep
      rPropDef_persistently
      rPropDef_later.
  Proof using Type.
    constructor.
    - unfold dist, rPropDef_dist; intros _.
      by apply later_ne.
    - by apply later_mono.
    - by apply later_intro.
    - by apply @later_forall_2.
    - by apply @later_exist_false.
    - by apply later_sep_1.
    - by apply later_sep_2.
    - by apply later_persistently_1.
    - by apply later_persistently_2.
    - by apply later_false_em.
  Qed.

  Definition bi_persistently_mixin :
    BiPersistentlyMixin
      rPropDef_entails
      rPropDef_empty
      rPropDef_and
      rPropDef_exist
      rPropDef_sep
      rPropDef_persistently.
  Proof using Type.
    constructor.
    - unfold dist, rPropDef_dist; intros _.
      by apply persistently_ne.
    - by apply persistently_mono.
    - by apply persistently_idemp_2.
    - by apply persistently_emp_2.
    - by apply persistently_and_2.
    - by apply @persistently_exist_1.
    - by apply persistently_absorbing.
    - by apply persistently_and_sep_elim.
  Qed.

  (** ** RProp is a BI *)

  Global Canonical Structure rProp : bi :=
    {|
      bi_car := rPropDef;
      bi_dist := dist;
      bi_equiv := equiv;
      bi_entails := rPropDef_entails;
      bi_emp := rPropDef_empty;
      bi_pure := rPropDef_pure;
      bi_and := rPropDef_and;
      bi_or := rPropDef_or;
      bi_impl := rPropDef_impl;
      bi_forall := rPropDef_forall;
      bi_exist := rPropDef_exist;
      bi_sep := rPropDef_sep;
      bi_wand := rPropDef_wand;
      bi_persistently := rPropDef_persistently;
      bi_later := rPropDef_later;
      bi_ofe_mixin := discrete_ofe_mixin equiv_equiv;
      bi_cofe_aux := discrete_cofe equiv_equiv;
      bi_bi_mixin := rProp_bi_mixin;
      bi_bi_persistently_mixin := bi_persistently_mixin;
      bi_bi_later_mixin := bi_later_mixin;
    |}.

  (** Extra BI instances *)

  Global Instance rProp_persistently_forall : BiPersistentlyForall rProp.
  Proof using Type.
    intros Q Ψ.
    unfold bi_entails, bi_persistently, bi_forall.
    apply persistently_forall_2.
  Qed.

  Global Instance rProp_pure_forall : BiPureForall rProp.
  Proof using Type.
    intros A φ.
    unfold bi_entails, bi_pure, bi_forall.
    apply pure_forall_2.
  Qed.
End BI_def.

Notation "'⌜' φ '⌟'" :=
  (bi_affinely (bi_pure φ%type%stdpp))%I
    (at level 0, φ constr at level 200) : bi_scope.
