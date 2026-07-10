From RSL Require Import Prelude.
From RSL Require Import Logic.Logic.

(** ** Memory Connectives *)

Local Definition mem_assert addr x (m: memory) : Prop :=
  ∃ loc, val_to_loc addr = Some loc ∧ m = {[loc := x]}.

Definition rlogic_mem_t_assert addr x : rlogic :=
  fun mt ms => mem_assert addr x mt ∧ ms = ∅.

Definition rlogic_mem_s_assert addr x : rlogic :=
  fun mt ms => mt = ∅ ∧ mem_assert addr x ms.

Notation "l '→ₜ' v" :=
  ⦇ rlogic_mem_t_assert l%positive v%Z ⦈
    (at level 70, no associativity, format "l →ₜ v") : rlogic_scope.

Notation "l '→ₛ' v" :=
  ⦇ rlogic_mem_s_assert l%positive v%Z ⦈
    (at level 70, no associativity, format "l →ₛ v") : rlogic_scope.

Notation "addrt 'ₜ⟨' P '⟩ₛ' addrs" :=
  ⦇ ∃ vt vs, addrt →ₜ vt ∗ addrs →ₛ vs ∗ ⌜P vt vs⌝ ⦈
    (at level 70, no associativity) : rlogic_scope.

Notation "addrs 'ₛ⟨' P '⟩ₜ' addrt" :=
  ⦇ ∃ vt vs, addrt →ₜ vt ∗ addrs →ₛ vs ∗ ⌜P vt vs⌝ ⦈
    (at level 70, no associativity) : rlogic_scope.

Notation "addrt 'ₜ~ₛ' addrs" :=
  ⦇ ∃ v, addrt →ₜ v ∗ addrs →ₛ v ⦈
    (at level 70, no associativity) : rlogic_scope.

Notation "addrs 'ₛ~ₜ' addrt" :=
  ⦇ ∃ v, addrt →ₜ v ∗ addrs →ₛ v ⦈
    (at level 70, no associativity) : rlogic_scope.
