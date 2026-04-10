From Stdlib Require Import Utf8.

From RSL Require Import RTL.
From RSL Require Import Semantics.

(* Set Mangle Names. *)

Definition oProp : Type := memory -> nat -> Prop.
Definition sProp : Type := regmap -> oProp.

Definition postcondition : Type := val -> memory -> Prop.
Definition precondition : Type := list val -> memory -> Prop.

Definition lift_oProp (P : oProp) : sProp :=  fun _ => P.
Coercion lift_oProp : oProp >-> sProp.

Class Logic (L: Type) :=
  {
    logic_and : L -> L -> L;
    logic_or  : L -> L -> L;
    logic_impl : L -> L -> L;
    logic_not : L -> L;
    logic_exists {X: Type}: (X -> L) -> L;
    logic_forall {X: Type}: (X -> L) -> L;

    logic_empty_entails : L -> Prop;
    logic_pure : Prop -> L;
    logic_memory_pure : (memory -> Prop) -> L;
    logic_later : L -> L;
    logic_always : L -> L;
    logic_memory_entails : L -> L;
  }.

Declare Scope logic_scope.
Delimit Scope logic_scope with logic.
Bind Scope logic_scope with oProp.
Bind Scope logic_scope with sProp.

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

Notation "'⟨' P '⟩'" := P%logic.

(* Definition logic_entails `{Logic L} (P Q : L) : Prop := *)
(*   logic_empty_entails (logic_impl P Q). *)
(* Notation "P ⊢ Q" := *)
(*   (logic_entails P%logic Q%logic) *)
(*     (at level 99, right associativity). *)

Instance oProp_logic : Logic oProp :=
  {|
    logic_and P Q := fun m n => P m n ∧ Q m n;
    logic_or P Q := fun m n => P m n ∨ Q m n;
    logic_impl P Q := fun m n => P m n -> Q m n;
    logic_not P := fun m n => ~ P m n;
    logic_exists X f := fun m n => ∃ x, f x m n;
    logic_forall X f := fun m n => ∀ x, f x m n;

    logic_empty_entails P := ∀ m n, P m n;
    logic_pure P := fun _ _ => P;
    logic_memory_pure P := fun m _ => P m;
    logic_later P :=
      fun m n =>
        match n with
        | O => True
        | S n => P m n
        end;

    logic_always P := fun m _ => ∀ n, P m n;
    logic_memory_entails P := fun _ n => ∀ m, P m n;
  |}.

Definition oProp_update (f: memory -> option memory) (P: oProp) : oProp :=
  fun m n => ∃ m', f m = Some m' ∧ P m' n.

Class oPropSetMem (L : Type) := logic_set_mem : val -> val -> L -> L.
Notation "'⟦' addr '<-' v '⟧' P" :=
  (logic_set_mem addr v P)
    (at level 20, P at level 20, right associativity,
       format "⟦ addr <- v ⟧  P").

Definition oProp_set (addr: val) (v: val) (P: oProp) : oProp :=
  oProp_update (set_at addr v) P.
Instance set_mem_oProp : oPropSetMem oProp := oProp_set.

Instance set_mem_sProp : oPropSetMem sProp :=
  fun addr v P ρ => oProp_set addr v (P ρ).

Definition oProp_assert (addr: val) (v: val) : oProp :=
  fun m n => get_at addr m = Some v.
Notation "l '↦' v" :=
  (oProp_assert l v)
    (at level 70, no associativity, format "l ↦ v") : logic_scope.

Instance sProp_logic : Logic sProp :=
  {|
    logic_and P Q := fun ρ => logic_and (P ρ) (Q ρ);
    logic_or P Q := fun ρ => logic_or (P ρ) (Q ρ);
    logic_impl P Q := fun ρ => logic_impl (P ρ) (Q ρ);
    logic_not P := fun ρ => logic_not (P ρ);
    logic_exists X f := fun ρ => logic_exists (fun x => f x ρ);
    logic_forall X f := fun ρ => logic_forall (fun x => f x ρ);

    logic_empty_entails P := ∀ ρ, logic_empty_entails (P ρ);
    logic_pure P := fun _ => logic_pure P;
    logic_memory_pure P := fun _ => logic_memory_pure P;
    logic_later P := fun ρ => logic_later (P ρ);
    logic_always P := fun ρ => logic_always (P ρ);
    logic_memory_entails P := fun ρ => logic_memory_entails (P ρ);
  |}.

Definition sProp_set_reg (r : reg) (v : val) (P : sProp) : sProp :=
  fun ρ => P (set_reg r v ρ).
Notation "'⟦' dst '<-ᵣ' v '⟧' P" :=
  (sProp_set_reg dst v P)
    (at level 20, P at level 20, right associativity,
       format "⟦ dst <-ᵣ v ⟧  P") : logic_scope.

Class LogicAssertReg (R V : Type) := logic_assert_reg : R -> V -> sProp.
Notation "r '↦ᵣ' v" :=
  (logic_assert_reg r v)
    (at level 70, no associativity, format "r ↦ᵣ v").

Definition sProp_assert_reg (r : reg) (v : val) : sProp :=
  fun ρ _ _ => get_reg r ρ = v.
Instance assert_reg_single : LogicAssertReg reg val :=
  sProp_assert_reg.

Definition sProp_assert_regs (rs : list reg) (vs : list val) : sProp :=
  fun ρ _ _ => get_regs rs ρ = vs.
Instance assert_reg_list : LogicAssertReg (list reg) (list val) :=
  sProp_assert_regs.

Definition sProp_register_entails (P : sProp) : sProp :=
  fun _ m n => ∀ ρ, P ρ m n.

Notation "'⊢ᵨ' P" :=
  (sProp_register_entails P)
    (at level 99, right associativity) : logic_scope.

Create HintDb custom_anyProp discriminated.

Hint Unfold
  lift_oProp
  logic_and
  logic_or
  logic_impl
  logic_not
  logic_exists
  logic_forall
  (* logic_entails *)
  logic_empty_entails
  logic_pure
  logic_later
  logic_always
  logic_memory_entails

  oProp_update
  oProp_set
  oProp_assert

  sProp_set_reg
  sProp_assert_reg
  sProp_assert_regs

  logic_assert_reg
  assert_reg_single
  assert_reg_list

  sProp_register_entails

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
