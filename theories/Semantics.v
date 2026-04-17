From stdpp Require Import prelude.

From RSL Require Import RTL.
From RSL Require Import Notations.

Import RTLNotations.

(* Set Mangle Names. *)

Fixpoint init_regs (vl: list val) (rl: list reg) : regmap :=
  match rl, vl with
  | r :: rs, v :: vs => <[r := v]>(init_regs vs rs)
  | _, _ => ∅
  end.

Inductive stackframe : Type :=
| Stackframe
    (res: reg) (* where to store the result *)
    (f: function) (* calling function *)
    (pc: node) (* program point in caller function *)
    (ρ: regmap) (* state in caller function *)
.

Inductive pcstate : Type :=
| State
    (f: function) (* current function *)
    (pc: node) (* current program point in c *)
    (ρ: regmap) (* register state *)

| CallState
    (f: function) (* function to call *)
    (args: list val) (* arguments to the call *)

| ReturnState
    (v: val). (* return value for the call *)

Definition state : Type := list stackframe * pcstate * memory.

Reserved Notation "P '⊨' s '->>' t" (at level 60, right associativity).

Inductive step (P: program) : state -> state -> Prop :=
| exec_Inop: forall σ m ρ f pc pc',
  f@pc is <{ nop -> pc' }> ->
  P ⊨ (σ, State f pc ρ, m) ->> (σ, State f pc' ρ, m)

| exec_Iret: forall σ m ρ f pc r v,
  f@pc is <{ ret r }> ->
  get_reg r ρ = v ->
  P ⊨ (σ, State f pc ρ, m) ->> (σ, ReturnState v, m)

| exec_Iop: forall σ m ρ f pc op args dst pc' ρ' v,
  f@pc is <{ dst := @op args -> pc' }> ->
  eval_op op (get_regs args ρ) = Some v ->
  set_reg dst v ρ = ρ' ->
  P ⊨ (σ, State f pc ρ, m) ->> (σ, State f pc' ρ', m)

| exec_Iload: forall σ m ρ f pc dst src pc' ρ' addr v,
  f@pc is <{ dst := !src -> pc' }> ->
  get_reg src ρ = addr ->
  get_at addr m = Some v ->
  set_reg dst v ρ = ρ' ->
  P ⊨ (σ, State f pc ρ, m) ->> (σ, State f pc' ρ', m)

| exec_Istore: forall σ m ρ f pc dst src pc' m' addr v,
  f@pc is <{ !dst := src -> pc' }> ->
  get_reg dst ρ = addr ->
  get_reg src ρ = v ->
  set_at addr v m = Some m' ->
  P ⊨ (σ, State f pc ρ, m) ->> (σ, State f pc' ρ, m')

| exec_Icond: forall  σ m ρ f pc cond ifso ifnot v pc',
  f@pc is <{ if cond then goto ifso else goto ifnot }> ->
  get_reg cond ρ = v ->
  pc' = (if Z.eqb v 0 then ifso else ifnot) ->
  P ⊨ (σ, State f pc ρ, m) ->> (σ, State f pc' ρ, m)

| exec_Icall: forall σ m ρ f pc dst sig args pc' σ' fn,
  f@pc is <{ dst := @call sig args -> pc' }> ->
  find_fun P sig = Some fn ->
  Stackframe dst f pc' ρ :: σ = σ' ->
  P ⊨ (σ, State f pc ρ, m) ->> (σ', CallState fn (get_regs args ρ), m)

| exec_function: forall σ m ρ f args,
  length args = length (fn_regs f) ->
  init_regs args (fn_regs f) = ρ ->
  P ⊨ (σ, CallState f args, m) ->> (σ, State f (fn_entrypoint f) ρ, m)

| exec_return: forall σ m ρ f pc dst v ρ',
  set_reg dst v ρ = ρ' ->
  P ⊨ (Stackframe dst f pc ρ :: σ, ReturnState v, m) ->> (σ, State f pc ρ', m)

where "P '⊨' s '->>' t" := (step P s t).

Notation "P '⊨' s '->>*' t" :=
  (rtc (step P) s t)  (at level 60, right associativity).

Notation "P '⊨' s '-{' n '}>' t" :=
  (nsteps (step P) n s t)  (at level 60, right associativity).

Variant final : state -> Prop :=
| FinalState : ∀ v m, final ([], ReturnState v, m).

Definition can_progress (P: program) s := ∃ t, P ⊨ s ->> t.

Definition stuck (P: program) s := ~(can_progress P s) ∧ ~(final s).
