From RSL Require Import Prelude.

From stdpp Require Export fin_maps fin_map_dom.

(** ** Logic Definition  *)

Definition rlogic : Type :=
  memory -> memory -> Prop.

(* Notations scope *)
Declare Scope rlogic_scope.
Delimit Scope rlogic_scope with rlogic.
Bind Scope rlogic_scope with rlogic.

(** ** Logical Connectives *)

Section LogicOp.

  Definition rlogic_and (P Q: rlogic) : rlogic :=
    fun mt ms => P mt ms ∧ Q mt ms.

  Definition rlogic_sep_and (P Q: rlogic) : rlogic :=
    fun mt ms =>
      ∃ mt1 mt2 ms1 ms2,
        mt1 ##ₘ mt2 ∧
        ms1 ##ₘ ms2 ∧
        mt1 ∪ mt2 = mt ∧
        ms1 ∪ ms2 = ms ∧
        P mt1 ms1 ∧
        Q mt2 ms2.

  Definition rlogic_or (P Q: rlogic) : rlogic :=
    fun mt ms => P mt ms ∨ Q mt ms.

  Definition rlogic_impl (P Q: rlogic) : rlogic :=
    fun mt ms => P mt ms -> Q mt ms.

  Definition rlogic_wand (P Q: rlogic) : rlogic :=
    fun mt ms =>
      ∀ mt' ms',
      mt' ##ₘ mt ->
      ms' ##ₘ ms ->
      P mt' ms' ->
      Q (mt ∪ mt') (ms ∪ ms').

  Definition rlogic_not (P: rlogic) : rlogic :=
    fun mt ms => ~ P mt ms.

  Definition rlogic_exists {X: Type} (f: X -> rlogic) : rlogic :=
    fun mt ms => ∃ x, f x mt ms.

  Definition rlogic_forall {X: Type} (f: X -> rlogic) : rlogic :=
    fun mt ms => ∀ x, f x mt ms.

  Definition rlogic_pure (P: Prop) : rlogic :=
    fun mt ms => mt = ∅ ∧ ms = ∅ ∧ P.

  Definition rlogic_empty : rlogic :=
    fun mt ms => mt = ∅ ∧ ms = ∅.

  Definition rlogic_entails (P: rlogic) : Prop :=
    P ∅ ∅.

End LogicOp.

Notation "x ∧ y" :=
  (rlogic_and x y)
    (at level 80, y constr at level 80, right associativity) : rlogic_scope.

Notation "x ∗ y" :=
  (rlogic_sep_and x y)
    (at level 80, y constr at level 80, right associativity) : rlogic_scope.

Notation "x ∨ y" :=
  (rlogic_or x y)
    (at level 85, y constr at level 85, right associativity) : rlogic_scope.

Notation "x → y" := (rlogic_impl x y)
  (at level 99, y at level 200, right associativity) : rlogic_scope.

Notation "x -> y" := (rlogic_impl x y)
  (at level 99, y at level 200, right associativity) : rlogic_scope.

Notation "x -* y" := (rlogic_wand x y)
  (at level 99, y at level 200, right associativity) : rlogic_scope.

Notation "~ x" :=
  (rlogic_not x)
    (at level 75, x constr at level 75, right associativity) : rlogic_scope.

Notation "¬ x" :=
  (rlogic_not x)
    (at level 75, x constr at level 75, right associativity) : rlogic_scope.

Notation "∀ x .. y , P" :=
  (rlogic_forall (fun x => .. (rlogic_forall (fun y => P)) ..))
    (at level 10, x binder, y binder, P at level 200,
     format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : rlogic_scope.

Notation "∃ x .. y , P" :=
  (rlogic_exists (fun x => .. (rlogic_exists (fun y => P)) ..))
    (at level 10, x binder, y binder, P at level 200,
     format "'[ ' '[ ' ∃ x .. y ']' , '/' P ']'") : rlogic_scope.

Notation "⌜ P ⌝" :=
  (rlogic_pure P) (at level 0, format "⌜ P ⌝") : rlogic_scope.

Notation "⦇ P ⦈" :=
  (P)%rlogic (at level 0, P at level 200, format "⦇ P ⦈").

Notation "⊨ P" :=
  (rlogic_entails P%rlogic) (at level 99, right associativity).

Notation "⌜⌝" := (rlogic_empty) (at level 0) : rlogic_scope.

Global Abbreviation emp := (rlogic_empty).

(** ** Memory Connectives *)

Section MemoryOp.
  Definition rlogic_mem_t_assert addr v : rlogic :=
    fun mt _ => get_at addr mt = Some v.

  Definition rlogic_mem_s_assert addr v : rlogic :=
    fun _ ms => get_at addr ms = Some v.

  Definition rlogic_mem_same_at P addrt addrs : rlogic :=
    fun mt ms =>
      P (get_at addrt mt) (get_at addrs ms).

End MemoryOp.

Notation "l '→ₜ' v" :=
  (rlogic_mem_t_assert l%positive v%Z)
    (at level 70, no associativity, format "l →ₜ v") : rlogic_scope.

Notation "l '→ₛ' v" :=
  (rlogic_mem_s_assert l%positive v%Z)
    (at level 70, no associativity, format "l →ₛ v") : rlogic_scope.

Notation "addrt 'ₜ⟨' P '⟩ₛ' addrs" :=
  (rlogic_mem_same_at P addrt%positive addrs%positive)
    (at level 70, no associativity) : rlogic_scope.

Notation "addrs 'ₛ⟨' P '⟩ₜ' addrt" :=
  (rlogic_mem_same_at P addrt%positive addrs%positive)
    (at level 70, no associativity) : rlogic_scope.

Notation "addrt 'ₜ~ₛ' addrs" :=
  (rlogic_mem_same_at eq addrt%positive addrs%positive)
    (at level 70, no associativity) : rlogic_scope.

Notation "addrs 'ₛ~ₜ' addrt" :=
  (rlogic_mem_same_at eq addrt%positive addrs%positive)
    (at level 70, no associativity) : rlogic_scope.

(** ** Auto unfolding *)

Create HintDb custom_rlogic discriminated.

Hint Unfold
  rlogic_and
  rlogic_sep_and
  rlogic_or
  rlogic_impl
  rlogic_wand
  rlogic_not
  rlogic_exists
  rlogic_forall

  rlogic_pure
  rlogic_empty
  rlogic_entails

  rlogic_mem_t_assert
  rlogic_mem_s_assert
  rlogic_mem_same_at
  : custom_rlogic.

Ltac simp :=
  autounfold with custom_rlogic in *;
  cbn beta iota zeta delta in *.
