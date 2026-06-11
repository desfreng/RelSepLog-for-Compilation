From RSL Require Import Prelude.
From RSL Require Import RelLogic.Logic.

(** ** Memory Connectives *)

Section MemoryOp.
  Definition rlogic_mem_t_assert addr v : rlogic :=
    fun mt _ =>
      ∃ loc, val_to_loc addr = Some loc ∧ mt = {[loc := v]}.

  Definition rlogic_mem_s_assert addr v : rlogic :=
    fun _ ms =>
      ∃ loc, val_to_loc addr = Some loc ∧ ms = {[loc := v]}.

  Definition rlogic_mem_same_at P addrt addrs : rlogic :=
    fun mt ms =>
      ∃ loct locs vt vs,
        val_to_loc addrt = Some loct ∧
        val_to_loc addrs = Some locs ∧
        mt = {[loct := vt]} ∧
        ms = {[locs := vs]} ∧
        P vt vs.

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
