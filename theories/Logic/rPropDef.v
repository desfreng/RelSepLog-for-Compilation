From RSL Require Import Prelude.

From RSL.Commons Require Import Tactics.
From RSL.Commons Require Export WfRel Memory.

From Ltac2 Require Ltac2 Printf.

(** * Logic Definition *)

Record rPropDef : Type :=
  {
    rProp_holds : memory -> memory -> Prop;

    (* rProp_mono j i mt ms : ∀ j' i', *)
    (*   j ⊑ j' -> *)
    (*   i ⊑ i' -> *)
    (*   rProp_holds j i mt ms -> *)
    (*   rProp_holds j' i' mt ms; *)
  }.

Section rPropDef_def.
  (* Context {J I: WfRel}. *)
  (* Abbreviation rPropDef := (rPropDef J I). *)

  Local Coercion rProp_holds : rPropDef >-> Funclass.

  (** ** Entailement *)

  Local Definition entails_def (P Q: rPropDef) : Prop :=
    ∀ mt ms, P mt ms -> Q mt ms.

  Local Definition entails_aux : seal (@entails_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_entails := unseal entails_aux.
  Local Lemma entails_unseal : @rPropDef_entails = @entails_def.
  Proof using Type. by apply seal_eq. Qed.

  Global Instance rPropDef_equiv : Equiv rPropDef :=
    fun P Q => rPropDef_entails P Q ∧ rPropDef_entails Q P.

  (** ** Pure lifting *)

  Local Program Definition pure_def (P: Prop) : rPropDef :=
    {| rProp_holds _ _ := P |}.

  Local Definition pure_aux : seal (@pure_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_pure := unseal pure_aux.
  Local Lemma pure_unseal : @rPropDef_pure = @pure_def.
  Proof using Type. by apply seal_eq. Qed.

  (** ** Empty Predicate *)

  Local Program Definition empty_def : rPropDef :=
    {| rProp_holds mt ms := mt = ∅ ∧ ms = ∅ |}.

  Local Definition empty_aux : seal (@empty_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_empty := unseal empty_aux.
  Local Lemma empty_unseal : @rPropDef_empty = @empty_def.
  Proof using Type. by apply seal_eq. Qed.

  (** ** Logical Connectives *)

  (** *** And *)

  Local Program Definition and_def (P Q: rPropDef) : rPropDef :=
    {| rProp_holds mt ms := P mt ms ∧ Q mt ms |}.

  Local Definition and_aux : seal (@and_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_and := unseal and_aux.
  Local Lemma and_unseal : @rPropDef_and = @and_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Or *)

  Local Program Definition or_def (P Q: rPropDef) : rPropDef :=
    {| rProp_holds mt ms := P mt ms ∨ Q mt ms |}.

  Local Definition or_aux : seal (@or_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_or := unseal or_aux.
  Local Lemma or_unseal : @rPropDef_or = @or_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Implication *)

  Local Program Definition impl_def (P Q: rPropDef) : rPropDef :=
    {| rProp_holds mt ms :=
         P mt ms ->
         Q mt ms
    |}.

  Local Definition impl_aux : seal (@impl_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_impl := unseal impl_aux.
  Local Lemma impl_unseal : @rPropDef_impl = @impl_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Forall **)

  Local Program Definition forall_def : ∀ X (f: X -> rPropDef), rPropDef :=
    fun X f => {| rProp_holds mt ms := ∀ x: X, f x mt ms |}.

  Local Definition forall_aux : seal (@forall_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_forall := unseal forall_aux.
  Local Lemma forall_unseal : @rPropDef_forall = @forall_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Exist *)

  Local Program Definition exist_def : ∀ X (f: X -> rPropDef), rPropDef :=
    fun X f => {| rProp_holds mt ms := ∃ x: X, f x mt ms |}.

  Local Definition exist_aux : seal (@exist_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_exist := unseal exist_aux.
  Local Lemma exist_unseal : @rPropDef_exist = @exist_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Separating conjunction *)

  Local Program Definition sep_def (P Q: rPropDef) : rPropDef :=
    {| rProp_holds mt ms :=
        ∃ mtP msP mtQ msQ : memory,
          mtP ##ₘ mtQ ∧
          msP ##ₘ msQ ∧
          mtP ∪ mtQ = mt ∧
          msP ∪ msQ = ms ∧
          P mtP msP ∧
          Q mtQ msQ
    |}.

  Local Definition sep_aux : seal (@sep_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_sep := unseal sep_aux.
  Local Lemma sep_unseal : @rPropDef_sep = @sep_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Separating implication *)

  Local Program Definition wand_def (P Q: rPropDef) : rPropDef :=
    {| rProp_holds mt ms :=
        ∀ mtP msP : memory,
         mtP ##ₘ mt ->
         msP ##ₘ ms ->
         P mtP msP ->
         Q (mt ∪ mtP) (ms ∪ msP)
    |}.

  Local Definition wand_aux : seal (@wand_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_wand := unseal wand_aux.
  Local Lemma wand_unseal : @rPropDef_wand = @wand_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Persistent connective *)

  Local Program Definition persistently_def (P: rPropDef) : rPropDef :=
    {| rProp_holds mt ms := P ∅ ∅ |}.

  Local Definition persistently_aux : seal (@persistently_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_persistently := unseal persistently_aux.
  Local Lemma persistently_unseal : @rPropDef_persistently = @persistently_def.
  Proof using Type. by apply seal_eq. Qed.

  (** *** Later connective *)

  Local Program Definition later_def (P: rPropDef) : rPropDef :=
    {| rProp_holds mt ms := P mt ms |}.

  Local Definition later_aux : seal (@later_def).
  Proof using Type. by eexists. Qed.
  Definition rPropDef_later := unseal later_aux.
  Local Lemma later_unseal : @rPropDef_later = @later_def.
  Proof using Type. by apply seal_eq. Qed.

End rPropDef_def.

Module Tactic.
  Import Ltac2 Printf.

  Local Ltac2 to_unfold () : Std.reference list :=
    [
      reference:(rPropDef.entails_def);
      reference:(rPropDef.pure_def);
      reference:(rPropDef.empty_def);
      reference:(rPropDef.and_def);
      reference:(rPropDef.or_def);
      reference:(rPropDef.impl_def);
      reference:(rPropDef.forall_def);
      reference:(rPropDef.exist_def);
      reference:(rPropDef.sep_def);
      reference:(rPropDef.wand_def);
      reference:(rPropDef.persistently_def);
      reference:(rPropDef.later_def)
    ].

  Local Ltac2 to_rewrite () : constr list :=
    [
      constr:(rPropDef.entails_unseal);
      constr:(rPropDef.pure_unseal);
      constr:(rPropDef.empty_unseal);
      constr:(rPropDef.and_unseal);
      constr:(rPropDef.or_unseal);
      constr:(rPropDef.impl_unseal);
      constr:(rPropDef.forall_unseal);
      constr:(rPropDef.exist_unseal);
      constr:(rPropDef.sep_unseal);
      constr:(rPropDef.wand_unseal);
      constr:(rPropDef.persistently_unseal);
      constr:(rPropDef.later_unseal)
    ].

  Ltac2 prep_goal cl :=
    let prep_list :=
      List.map
        (fun c => (c, Std.AllOccurrences))
        [
          reference:(equiv);
          reference:(rPropDef_equiv)
        ]
    in
    Std.unfold prep_list cl.

  Ltac2 unfold_mem () :=
    let all_goal :=
      {
        Std.on_hyps := None;
        Std.on_concl := Std.AllOccurrences
      }
    in
    Std.unfold [(reference:(memory), Std.AllOccurrences)] all_goal.

  Ltac2 unseal cl :=
    prep_goal cl;
    rewrite_list (to_rewrite ()) cl;
    unfold_list (to_unfold ()) cl;
    cbn [rProp_holds];
    unfold_mem ().

  Ltac2 Notation "unseal" cl(opt(seq("in", clause))) :=
    unseal (default_on_concl cl).

  Tactic Notation "unseal" := ltac2:(unseal).
End Tactic.
