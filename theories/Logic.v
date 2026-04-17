From stdpp Require Import base.

From RSL Require Import RTL.

(* Set Mangle Names. *)

Definition postcondition : Type := val -> memory -> Prop.
Definition precondition : Type := list val -> memory -> Prop.

Definition logic : Type := regmap -> memory -> nat -> Prop.

Declare Scope logic_scope.
Delimit Scope logic_scope with logic.
Bind Scope logic_scope with logic.

Definition logic_and (P Q: logic) : logic :=
  fun ρ m n => P ρ m n ∧ Q ρ m n.
Definition logic_or (P Q: logic) : logic :=
  fun ρ m n => P ρ m n ∨ Q ρ m n.
Definition logic_impl (P Q: logic) : logic :=
  fun ρ m n => P ρ m n -> Q ρ m n.
Definition logic_not (P: logic) : logic :=
  fun ρ m n => ~ P ρ m n.
Definition logic_exists {X: Type} (f: X -> logic) : logic :=
  fun ρ m n => ∃ x, f x ρ m n.
Definition logic_forall {X: Type} (f: X -> logic) : logic :=
  fun ρ m n => ∀ x, f x ρ m n.

Definition logic_empty_entails (P: logic) : Prop :=
  ∀ ρ m n, P ρ m n.
Definition logic_pure (P: Prop) : logic :=
  fun _ _ _ => P.
Definition logic_memory_pure (P: memory -> Prop) : logic :=
  fun _ m _ => P m.
Definition logic_later (P: logic) : logic :=
  fun ρ m n =>
    match n with
    | O => True
    | S n => P ρ m n
    end.

Definition logic_always (P: logic) : logic :=
  fun ρ m _ => ∀ n, P ρ m n.
Definition logic_memory_entails (P: logic) : logic :=
  fun ρ _ n => ∀ m, P ρ m n.
Definition logic_register_entails (P: logic) : logic :=
  fun _ m n => ∀ ρ, P ρ m n.

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

Notation "⊢ P" :=
  (logic_empty_entails P%logic)
    (at level 99, right associativity).
Notation "⌜ P ⌝" :=
  (logic_pure P)
    (at level 0, format "⌜ P ⌝") : logic_scope.
Notation "⌜ P ⌝ₘ" :=
  (logic_memory_pure P)
    (at level 0, format "⌜ P ⌝ₘ") : logic_scope.
Notation "▷ P" :=
  (logic_later P)
    (at level 20, right associativity, format "▷ P") : logic_scope.
Notation "□ P" :=
  (logic_always P)
    (at level 20, right associativity, format "□ P") : logic_scope.
Notation "'⊢ₘ' P" :=
  (logic_memory_entails P)
    (at level 99, right associativity) : logic_scope.
Notation "'⊢ᵨ' P" :=
  (logic_register_entails P)
    (at level 99, right associativity) : logic_scope.

Notation "'⟨' P '⟩'" := P%logic.

(* Definition logic_entails `{Logic L} (P Q : L) : Prop := *)
(*   logic_empty_entails (logic_impl P Q). *)
(* Notation "P ⊢ Q" := *)
(*   (logic_entails P%logic Q%logic) *)
(*     (at level 99, right associativity). *)

Definition logic_set_mem (addr: val) (v: val) (P: logic) : logic :=
  fun ρ m n => ∃ m', set_at addr v m = Some m' ∧ P ρ m' n.

Definition logic_assert_mem (addr: val) (v: val) : logic :=
  fun _ m _ => get_at addr m = Some v.

Definition logic_set_reg (r : reg) (v : val) (P : logic) : logic :=
  fun ρ m n => P (set_reg r v ρ) m n.

Notation "'⟦' addr '<-' v '⟧' P" :=
  (logic_set_mem addr v P)
    (at level 20, P at level 20, right associativity,
       format "⟦ addr <- v ⟧  P").

Notation "l '↦' v" :=
  (logic_assert_mem l v)
    (at level 70, no associativity, format "l ↦ v") : logic_scope.

Notation "'⟦' dst '<-ᵣ' v '⟧' P" :=
  (logic_set_reg dst v P)
    (at level 20, P at level 20, right associativity,
       format "⟦ dst <-ᵣ v ⟧  P") : logic_scope.

Class LogicAssertReg (R V : Type) := logic_assert_reg : R -> V -> logic.

Notation "r '↦ᵣ' v" :=
  (logic_assert_reg r v)
    (at level 70, no associativity, format "r ↦ᵣ v").

Instance assert_reg_single : LogicAssertReg reg val :=
  fun (r: reg) (v: val) ρ _ _ => get_reg r ρ = v.

Instance assert_reg_list : LogicAssertReg (list reg) (list val) :=
  fun (r: list reg) (v: list val) ρ _ _ => get_regs r ρ = v.

Create HintDb custom_anyProp discriminated.

Hint Unfold
  (* lift_oProp *)
  logic_and
  logic_or
  logic_impl
  logic_not
  logic_exists
  logic_forall
  (* logic_entails *)
  logic_empty_entails
  logic_pure
  logic_memory_pure
  logic_later
  logic_always
  logic_memory_entails
  logic_register_entails

  logic_set_mem
  logic_assert_mem

  logic_set_reg
  logic_assert_reg

  logic_assert_reg
  assert_reg_single
  assert_reg_list

: custom_anyProp.

Ltac unfold_Prop :=
  autounfold with custom_anyProp in *;
  cbv beta in *;
  simpl in *.

Lemma löb_weak P :
  (⊢ ▷ P -> P) -> ⊢ P.
Proof.
  intros H ρ m n.
  induction n as [|n IH]; now apply H.
Qed.

Lemma löb P :
  (⊢ ▷ (⊢ᵨ ⊢ₘ P) -> P) -> ⊢ P.
Proof.
  intros H ρ m n.
  revert ρ m.
  induction n as [|n IH]; intros ρ m; now apply H.
Qed.
