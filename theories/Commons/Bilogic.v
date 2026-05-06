From RSL Require Import Prelude.

(* Set Mangle Names. *)

Definition bilogic : Type := (regmap * memory) -> (regmap * memory) -> Prop.

Declare Scope bilogic_scope.
Delimit Scope bilogic_scope with bilogic.
Bind Scope bilogic_scope with bilogic.

Definition bilogic_and (P Q: bilogic) : bilogic :=
  fun t s => P t s ∧ Q s t.
Definition bilogic_or (P Q: bilogic) : bilogic :=
  fun t s => P t s ∨ Q t s.
Definition bilogic_impl (P Q: bilogic) : bilogic :=
  fun t s => P t s -> Q t s.
Definition bilogic_not (P: bilogic) : bilogic :=
  fun t s => ~ P t s.
Definition bilogic_exists {X: Type} (f: X -> bilogic) : bilogic :=
  fun t s => ∃ x, f x t s.
Definition bilogic_forall {X: Type} (f: X -> bilogic) : bilogic :=
  fun t s => ∀ x, f x t s.

Definition bilogic_empty_entails (P: bilogic) : Prop :=
  ∀ t s, P t s.
Definition bilogic_pure (P: Prop) : bilogic :=
  fun _ _ => P.
Definition bilogic_memory_pure (P: memory -> memory -> Prop) : bilogic :=
  fun '(_, mₜ) '(_, mₛ) => P mₜ mₛ.

Notation "P ∧ Q" :=
  (bilogic_and P Q) : bilogic_scope.
Notation "P ∨ Q" :=
  (bilogic_or P Q)  : bilogic_scope.
Notation "P -> Q" :=
  (bilogic_impl P Q) : bilogic_scope.
Notation "~ P" :=
  (bilogic_not P) : bilogic_scope.
Notation "'∃' x .. y , p" :=
  (bilogic_exists (fun x => .. (bilogic_exists (fun y => p)) ..)) : bilogic_scope.
Notation "'∀' x .. y , p" :=
  (bilogic_forall (fun x => .. (bilogic_forall (fun y => p)) ..)) : bilogic_scope.

Notation "⊨ P" :=
  (bilogic_empty_entails P%bilogic)
    (at level 99, right associativity).
Notation "⌜ P ⌝" :=
  (bilogic_pure P)
    (at level 0, format "⌜ P ⌝") : bilogic_scope.
Notation "⌜ P ⌝ₘ" :=
  (bilogic_memory_pure P)
    (at level 0, format "⌜ P ⌝ₘ") : bilogic_scope.

(* Notation "'⟨' P '⟩'" := P%bilogic. *)

(* Definition bilogic_entails `{Bilogic L} (P Q : L) : Prop := *)
(*   bilogic_empty_entails (bilogic_impl P Q). *)
(* Notation "P ⊢ Q" := *)
(*   (bilogic_entails P%bilogic Q%bilogic) *)
(*     (at level 99, right associativity). *)

Definition bilogic_assert_t_mem (addr: val) (v: val) : bilogic :=
  fun '(_, m) _ => get_at addr m = Some v.

Definition bilogic_assert_s_mem (addr: val) (v: val) : bilogic :=
  fun _ '(_, m) => get_at addr m = Some v.

Notation "l '→ₜ' v" :=
  (bilogic_assert_t_mem l%positive v%Z)
    (at level 70, no associativity, format "l →ₜ v") : bilogic_scope.

Notation "l '→ₛ' v" :=
  (bilogic_assert_s_mem l%positive v%Z)
    (at level 70, no associativity, format "l →ₛ v") : bilogic_scope.

Class BilogicAssertTReg (R V : Type) := bilogic_assert_t_reg : R -> V -> bilogic.

Notation "r '↪ₜ' v" :=
  (bilogic_assert_t_reg r%nat v%Z)
    (at level 70, no associativity, format "r ↪ₜ v").

Instance assert_reg_t_single : BilogicAssertTReg reg val :=
  fun (r: reg) (v: val) '(ρ, _) _ => get_reg r ρ = v.

Instance assert_reg_t_list : BilogicAssertTReg (list reg) (list val) :=
  fun (r: list reg) (v: list val) '(ρ, _) _ => get_regs r ρ = v.

Class BilogicAssertSReg (R V : Type) := bilogic_assert_s_reg : R -> V -> bilogic.

Notation "r '↪ₛ' v" :=
  (bilogic_assert_s_reg r%nat v%Z)
    (at level 70, no associativity, format "r ↪ₛ v").

Instance assert_reg_s_single : BilogicAssertSReg reg val :=
  fun (r: reg) (v: val) _ '(ρ, _) => get_reg r ρ = v.

Instance assert_reg_s_list : BilogicAssertSReg (list reg) (list val) :=
  fun (r: list reg) (v: list val) _ '(ρ, _) => get_regs r ρ = v.

Definition logic_set_t_mem (addr: val) (v: val) (P: bilogic) : bilogic :=
  fun '(ρₜ, m) s => ∃ m', set_at addr v m = Some m' ∧ P (ρₜ, m') s.

Definition logic_set_s_mem (addr: val) (v: val) (P: bilogic) : bilogic :=
  fun t '(ρₛ, m) => ∃ m', set_at addr v m = Some m' ∧ P t (ρₛ, m').

Definition logic_set_t_reg (r : reg) (v : val) (P : bilogic) : bilogic :=
  fun '(ρₜ, m) s => P (set_reg r v ρₜ, m) s.

Definition logic_set_s_reg (r : reg) (v : val) (P : bilogic) : bilogic :=
  fun t '(ρₛ, m) => P t (set_reg r v ρₛ, m).

Notation "'⟦' addr '←ₜ' v '⟧' P" :=
  (logic_set_t_mem addr v P)
    (at level 20, P at level 20, right associativity).

Notation "'⟦' addr '←ₛ' v '⟧' P" :=
  (logic_set_s_mem addr v P)
    (at level 20, P at level 20, right associativity).

Notation "'⟦' addrt '←ₜ' vt ',' addrs '←ₛ' vs '⟧' P" :=
  (logic_set_t_mem addrt vt (logic_set_s_mem addrs vs P))
    (at level 20, P at level 20, right associativity).

Notation "'⟦' r '↩ₜ' v '⟧' P" :=
  (logic_set_t_reg r v P)
    (at level 20, P at level 20, right associativity).

Notation "'⟦' r '↩ₛ' v '⟧' P" :=
  (logic_set_s_reg r v P)
    (at level 20, P at level 20, right associativity).

Notation "'⟦' addrt '↩ₜ' vt ',' addrs '↩ₛ' vs '⟧' P" :=
  (logic_set_t_reg addrt vt (logic_set_s_reg addrs vs P))
    (at level 20, P at level 20, right associativity).

Create HintDb custom_bilogic discriminated.

Hint Unfold
  (* lift_oProp *)
  bilogic_and
  bilogic_or
  bilogic_impl
  bilogic_not
  bilogic_exists
  bilogic_forall
  (* bilogic_entails *)
  bilogic_empty_entails
  bilogic_pure
  bilogic_memory_pure

  bilogic_assert_t_mem
  bilogic_assert_s_mem

  bilogic_assert_t_reg
  bilogic_assert_s_reg

  logic_set_t_mem
  logic_set_s_mem

  logic_set_t_reg
  logic_set_s_reg

  assert_reg_t_single
  assert_reg_s_list
  assert_reg_t_single
  assert_reg_s_list

: custom_bilogic.

Ltac unfold_bilogic :=
  autounfold with custom_bilogic in *;
  cbv beta in *;
  simpl in *.
