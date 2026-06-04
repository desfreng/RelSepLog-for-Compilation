From RSL Require Import Prelude.

(** ** Logic Definition  *)

Definition rlogic (Et Es : LEnv) : Type :=
  Et -> Es -> memory -> memory -> Prop.

(* Notations scope *)
Declare Scope rlogic_scope.
Delimit Scope rlogic_scope with rlogic.
Bind Scope rlogic_scope with rlogic.


(** ** Logical Connectives *)

Section LogicOp.
  Context {Et Es: LEnv}.

  Abbreviation rlogic := (rlogic Et Es).

  Definition rlogic_and (P Q: rlogic) : rlogic :=
    fun env_t env_s mt ms => P env_t env_s mt ms ∧ Q env_t env_s mt ms.

  Definition rlogic_or (P Q: rlogic) : rlogic :=
    fun env_t env_s mt ms => P env_t env_s mt ms ∨ Q env_t env_s mt ms.

  Definition rlogic_impl (P Q: rlogic) : rlogic :=
    fun env_t env_s mt ms => P env_t env_s mt ms -> Q env_t env_s mt ms.

  Definition rlogic_not (P: rlogic) : rlogic :=
    fun env_t env_s mt ms => ~ P env_t env_s mt ms.

  Definition rlogic_exists {X: Type} (f: X -> rlogic) : rlogic :=
    fun env_t env_s mt ms => ∃ x, f x env_t env_s mt ms.

  Definition rlogic_forall {X: Type} (f: X -> rlogic) : rlogic :=
    fun env_t env_s mt ms => ∀ x, f x env_t env_s mt ms.

  Definition rlogic_pure (P: Prop) : rlogic :=
    fun _ _ _ _ => P.

  Definition rlogic_memory_pure (P: memory -> memory -> Prop) : rlogic :=
    fun _ _ mt ms => P mt ms.

  Definition rlogic_env_t_pure (P: Et -> Prop) : rlogic :=
    fun env_t _ _ _  => P env_t.

  Definition rlogic_env_s_pure (P: Es -> Prop) : rlogic :=
    fun _ env_s _ _  => P env_s.

  Definition rlogic_entails (P: rlogic) : Prop :=
    ∀ env_t env_s mt ms, P env_t env_s mt ms.

  Global Instance top_rlogic : Top rlogic := rlogic_pure True.
  Global Instance bot_rlogic : Bottom rlogic := rlogic_pure False.

End LogicOp.

Notation "x ∧ y" :=
  (rlogic_and x y)
    (at level 80, y constr at level 80, right associativity) : rlogic_scope.

Notation "x ∨ y" :=
  (rlogic_or x y)
    (at level 85, y constr at level 85, right associativity) : rlogic_scope.

Notation "x → y" := (rlogic_impl x y)
  (at level 99, y at level 200, right associativity) : rlogic_scope.

Notation "x -> y" := (rlogic_impl x y)
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

Notation "⌜ P ⌝ₘ" :=
  (rlogic_memory_pure P) (at level 0, format "⌜ P ⌝ₘ") : rlogic_scope.

Notation "⌜ P ⌝ₜ" :=
  (rlogic_env_t_pure P) (at level 0, format "⌜ P ⌝ₜ") : rlogic_scope.

Notation "⌜ P ⌝ₛ" :=
  (rlogic_env_s_pure P) (at level 0, format "⌜ P ⌝ₛ") : rlogic_scope.

Notation "⦇ P ⦈" :=
  (P)%rlogic (at level 0, P at level 200, format "⦇ P ⦈").

Notation "⊨ P" :=
  (rlogic_entails P%rlogic) (at level 99, right associativity).

Notation "'True'" := (rlogic_pure True) (format "True") : rlogic_scope.
Notation "'False'" := (rlogic_pure False) (format "False") : rlogic_scope.


(** ** Memory Connectives *)

Section MemoryOp.
  Context {Et Es: LEnv}.

  Abbreviation rlogic := (rlogic Et Es).

  Definition rlogic_mem_t_assert addr v : rlogic :=
    fun _ _ mt _ => get_at addr mt = Some v.

  Definition rlogic_mem_s_assert addr v : rlogic :=
    fun _ _ _ ms => get_at addr ms = Some v.

  Definition rlogic_mem_t_set addr v (P: rlogic) : rlogic :=
    fun env_t env_s mt ms =>
      ∃ mt', set_at addr v mt = Some mt' ∧ P env_t env_s mt' ms.

  Definition rlogic_mem_s_set addr v (P: rlogic) : rlogic :=
    fun env_t env_s mt ms =>
      ∃ ms', set_at addr v ms = Some ms' ∧ P env_t env_s mt ms'.

  Definition rlogic_mem_same_at P addrt addrs : rlogic :=
    fun _ _ mt ms =>
      P (get_at addrt mt) (get_at addrs ms).

End MemoryOp.

(* Global Strategy opaque *)
(*   [ *)
(*     rlogic_mem_t_assert *)
(*     rlogic_mem_s_assert *)
(*     rlogic_mem_t_set *)
(*     rlogic_mem_s_set *)
(*     rlogic_mem_at_same *)
(*   ]. *)

Notation "l '→ₜ' v" :=
  (rlogic_mem_t_assert l%positive v%Z)
    (at level 70, no associativity, format "l →ₜ v") : rlogic_scope.

Notation "l '→ₛ' v" :=
  (rlogic_mem_s_assert l%positive v%Z)
    (at level 70, no associativity, format "l →ₛ v") : rlogic_scope.

Notation "'⟦' addr '←ₜ' v '⟧' P" :=
  (rlogic_mem_t_set addr%positive v%Z P)
    (at level 20, P at level 20, right associativity).

Notation "'⟦' addr '←ₛ' v '⟧' P" :=
  (rlogic_mem_s_set addr%positive v%Z P)
    (at level 20, P at level 20, right associativity).

Notation "'⟦' addrt '←ₜ' vt ',' addrs '←ₛ' vs '⟧' P" :=
  (rlogic_mem_t_set addrt%positive vt%Z
     (rlogic_mem_s_set addrs%positive vs%Z P))
    (at level 20, P at level 20, right associativity).

Notation "'⟦' addrs '←ₛ' vs ',' addrt '←ₜ' vt '⟧' P" :=
  (rlogic_mem_t_set addrt%positive vt%Z
     (rlogic_mem_s_set addrs%positive vs%Z P))
    (at level 20, P at level 20, right associativity).

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


(** ** Target Context Connectives *)

Section TargetOp.
  Context {Et Es: LEnv}.

  Abbreviation rlogic := (rlogic Et Es).

  Class RLogicTargetAssert (R V : Type) :=
    rlogic_env_t_assert : R -> V -> rlogic.

  Global Instance rlogic_env_t_assert_single : RLogicTargetAssert _ _ :=
    fun key val env_t _ _ _ =>
      get_data env_t key = Some val.

  Global Instance rlogic_env_t_assert_list : RLogicTargetAssert (list _) (list _) :=
    fun keys vals env_t _ _ _ =>
      mapM (get_data env_t) keys = Some vals.

  Definition rlogic_env_t_update key f (P : rlogic) : rlogic :=
    fun env_t env_s mt ms =>
      ∃ env_t',
        update_data env_t key f = Some env_t' ∧
        P env_t' env_s mt ms.

  Definition rlogic_env_t_set key val (P : rlogic) : rlogic :=
    rlogic_env_t_update key (fun _ => val) P.

End TargetOp.

(* Global Strategy opaque *)
(*   [ *)
(*     rlogic_env_t_assert *)
(*     rlogic_env_t_assert_helper *)
(*     rlogic_env_t_assert_single *)
(*     rlogic_env_t_assert_list *)
(*     rlogic_env_t_update *)
(*     rlogic_env_t_set *)
(*   ]. *)

Notation "r '⇒ₜ' v" :=
  (rlogic_env_t_assert r%nat v%Z)
    (at level 70, no associativity, format "r ⇒ₜ v").

Notation "'⟦' r '⇐ₜ' v '⟧' P" :=
  (rlogic_env_t_set r%nat v%Z P)
    (at level 20, P at level 20, right associativity).

Notation "'⟦' r '⇐ₜ' 'λ' v '.' f '⟧' P" :=
  (rlogic_env_t_update r%nat (fun v => f) P)
    (at level 20, v binder, P at level 20, right associativity).

Notation "'⟦' r '⇐ₜ' 'fun' v '.' f '⟧' P" :=
  (rlogic_env_t_update r%nat (fun v => f) P)
    (at level 20, v binder, P at level 20, right associativity).


(** ** Source Context Connectives *)

Section SourceOp.
  Context {Et Es: LEnv}.

  Abbreviation rlogic := (rlogic Et Es).

  Class RLogicSourceAssert (R V : Type) :=
    rlogic_env_s_assert : R -> V -> rlogic.

  Global Instance rlogic_env_s_assert_single : RLogicSourceAssert _ _ :=
    fun key val _ env_s _ _ =>
      get_data env_s key = Some val.

  Global Instance rlogic_env_s_assert_list : RLogicSourceAssert (list _) (list _) :=
    fun keys vals _ env_s _ _ =>
      mapM (get_data env_s) keys = Some vals.

  Definition rlogic_env_s_update key f (P : rlogic) : rlogic :=
    fun env_t env_s mt ms =>
      ∃ env_s',
        update_data env_s key f = Some env_s' ∧
        P env_t env_s' mt ms.

  Definition rlogic_env_s_set key val (P : rlogic) : rlogic :=
    rlogic_env_s_update key (fun _ => val) P.

End SourceOp.

(* Global Strategy opaque *)
(*   [ *)
(*     rlogic_env_s_assert *)
(*     rlogic_env_s_assert_helper *)
(*     rlogic_env_s_assert_single *)
(*     rlogic_env_s_assert_list *)
(*     rlogic_env_s_update *)
(*     rlogic_env_s_set *)
(*   ]. *)

Notation "r '⇒ₛ' v" :=
  (rlogic_env_s_assert r%nat v%Z)
    (at level 70, no associativity, format "r ⇒ₛ v").

Notation "'⟦' r '⇐ₛ' v '⟧' P" :=
  (rlogic_env_s_set r%nat v%Z P)
    (at level 20, P at level 20, right associativity).

Notation "'⟦' r '⇐ₛ' 'λ' v '.' f '⟧' P" :=
  (rlogic_env_s_update r%nat (fun v => f) P)
    (at level 20, v binder, P at level 20, right associativity).

Notation "'⟦' r '⇐ₛ' 'fun' v '.' f '⟧' P" :=
  (rlogic_env_s_update r%nat (fun v => f) P)
    (at level 20, v binder, P at level 20, right associativity).

(** ** Both Context Connectives *)

Section BothLEnvOp.
  Context {Et Es: LEnv}.

  Abbreviation rlogic := (rlogic Et Es).

  Definition rlogic_env_same_at P keyt keys : rlogic :=
    fun env_t env_s _ _ =>
      P (get_data env_t keyt) (get_data env_s keys).

End BothLEnvOp.

Notation "'⟦' rt '⇐ₜ' vt ',' rs '⇐ₛ' vs '⟧' P" :=
  (rlogic_env_t_set rt%nat vt%Z (rlogic_env_s_set rs%nat vs%Z P))
    (at level 20, P at level 20, right associativity).

Notation "'⟦' rs '⇐ₛ' vs ',' rt '⇐ₜ' vt '⟧' P" :=
  (rlogic_env_t_set rt%nat vt%Z (rlogic_env_s_set rs%nat vs%Z P))
    (at level 20, P at level 20, right associativity).

Notation "rt 'ₜ⟪' P '⟫ₛ' rs" :=
  (rlogic_env_same_at P rt%nat rs%nat)
    (at level 70, no associativity) : rlogic_scope.

Notation "rs 'ₛ⟪' P '⟫ₜ' rt" :=
  (rlogic_env_same_at P rt%nat rs%nat)
    (at level 70, no associativity) : rlogic_scope.

Notation "rt 'ₜ≈ₛ' rs" :=
  (rlogic_env_same_at eq rt%nat rs%nat)
    (at level 70, no associativity) : rlogic_scope.

Notation "rs 'ₛ≈ₜ' rt" :=
  (rlogic_env_same_at eq rt%nat rs%nat)
    (at level 70, no associativity) : rlogic_scope.

(** ** Auto unfolding *)

Create HintDb custom_rlogic discriminated.

Hint Unfold
  rlogic_and
  rlogic_or
  rlogic_impl
  rlogic_not
  rlogic_exists
  rlogic_forall

  rlogic_pure
  rlogic_memory_pure
  rlogic_env_t_pure
  rlogic_env_s_pure

  rlogic_entails

  rlogic_mem_t_assert
  rlogic_mem_s_assert
  rlogic_mem_same_at

  rlogic_env_t_assert
  rlogic_env_t_assert_single
  rlogic_env_t_assert_list

  rlogic_env_s_assert
  rlogic_env_s_assert_single
  rlogic_env_s_assert_list

  rlogic_env_same_at

  get_data : custom_rlogic.

Ltac simp :=
  autounfold with custom_rlogic in *;
  cbn beta iota zeta delta in *.
