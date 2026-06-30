From RSL Require Import Prelude.
From RSL Require Import Commons.RegisterBank.

Definition postcondition : Type := val -> memory -> Prop.
Definition precondition : Type := list val -> memory -> Prop.

Definition logic : Type := nat -> memory -> Prop.

Declare Scope logic_scope.
Delimit Scope logic_scope with logic.
Bind Scope logic_scope with logic.

Definition logic_and (P Q: logic) : logic :=
  fun n m => P n m ∧ Q n m.
Definition logic_or (P Q: logic) : logic :=
  fun n m => P n m ∨ Q n m.
Definition logic_impl (P Q: logic) : logic :=
  fun n m => P n m -> Q n m.
Definition logic_not (P: logic) : logic :=
  fun n m => ~ P n m.
Definition logic_exists {X: Type} (f: X -> logic) : logic :=
  fun n m => ∃ x, f x n m.
Definition logic_forall {X: Type} (f: X -> logic) : logic :=
  fun n m => ∀ x, f x n m.

Definition logic_entails (P Q: logic) : Prop :=
  ∀ n m, (logic_impl P Q) n m.
Definition logic_pure (P: Prop) : logic :=
  fun _ _ => P.
Definition logic_memory_pure (P: memory -> Prop) : logic :=
  fun _ m => P m.
Definition logic_later (P: logic) : logic :=
  fun n m =>
    match n with
    | O => True
    | S n => P n m
    end.

Definition logic_always (P: logic) : logic :=
  fun _ m => ∀ n, P n m.
Definition logic_memory_entails (P Q: logic) : logic :=
  fun n _ => ∀ m, (logic_impl P Q) n m.

Notation "P ∧ Q" :=
  (logic_and P Q) : logic_scope.
Notation "P ∨ Q" :=
  (logic_or P Q)  : logic_scope.
Notation "P -> Q" :=
  (logic_impl P Q) : logic_scope.
Notation "~ P" :=
  (logic_not P) : logic_scope.
Notation "'∃' x .. y , p" :=
  (logic_exists (fun x => .. (logic_exists (fun y => p)) ..)) : logic_scope.
Notation "'∀' x .. y , p" :=
  (logic_forall (fun x => .. (logic_forall (fun y => p)) ..)) : logic_scope.

Notation "P ⊩ Q" :=
  (logic_entails P%logic Q%logic)
    (at level 99, right associativity).
Notation "⌜ P ⌝" :=
  (logic_pure P)
    (at level 0, format "⌜ P ⌝") : logic_scope.
Notation "⌜ P ⌝ₘ" :=
  (logic_memory_pure P)
    (at level 0, format "⌜ P ⌝ₘ") : logic_scope.
Notation "▷ P" :=
  (logic_later P)
    (at level 20, right associativity) : logic_scope.
Notation "□ P" :=
  (logic_always P)
    (at level 20, right associativity) : logic_scope.
Notation "P '⊩ₘ' Q" :=
  (logic_memory_entails P Q)
    (at level 99, right associativity) : logic_scope.

Notation "⌜⌝" := (logic_pure True) (at level 0).

Notation "⦇ P ⦈" := (P)%logic (at level 0, P at level 200, format "⦇ P ⦈").

Definition logic_set_mem (addr: val) (v: val) (P: logic) : logic :=
  fun n m => ∃ m', set_at addr v m = Some m' ∧ P n m'.

Definition logic_assert_mem (addr: val) (v: val) : logic :=
  fun _ m => get_at addr m = Some v.

Notation "'⟦' l '<-' v '⟧' P" :=
  (logic_set_mem l%positive v%Z P)
    (at level 20, P at level 20, right associativity,
       format "⟦ l <- v ⟧  P").

Notation "l '↦' v" :=
  (logic_assert_mem l%positive v%Z)
    (at level 70, no associativity, format "l ↦ v") : logic_scope.

Create HintDb custom_anyProp discriminated.

Hint Unfold
  (* lift_oProp *)
  logic_and
  logic_or
  logic_impl
  logic_not
  logic_exists
  logic_forall
  logic_entails
  logic_pure
  logic_memory_pure
  logic_later
  logic_always
  logic_memory_entails

  logic_set_mem
  logic_assert_mem
: custom_anyProp.

Ltac unfold_Prop :=
  autounfold with custom_anyProp in *;
  cbv beta in *;
  simpl in *.

Lemma löb_weak P :
  (▷ P ⊩ P) -> ⌜⌝ ⊩ P.
Proof.
  intros H n m _.
  induction n as [|n IH]; now apply H.
Qed.

Lemma löb P :
  (▷ (⌜⌝ ⊩ₘ P) ⊩ P) -> ⌜⌝ ⊩ P.
Proof.
  intros H n.
  induction n as [|n IH]; intros m _; now apply H.
Qed.
