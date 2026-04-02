From Stdlib Require Import Utf8.

From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Relations.Relations.

From RSL Require Import Tactics.
From RSL Require Import NatMap.
From RSL Require Import RTL.
From RSL Require Import Notations.

Import RTLNotations.
Import ListNotations.

(* [regmap] is a mapping from registers to a value *)
Definition regmap : Type := NatMap.t val.

(* [memory] is a mapping from location to a value *)
Definition memory : Type := NatMap.t val.

Definition get_reg (ρ: regmap) (r: reg) : val :=
  match NatMap.find r ρ with
  | Some v => v
  | None => 0%Z (* Dummy val *)
  end.

Definition get_regs (ρ: regmap) (l: list reg) : list val :=
  map (fun r => get_reg ρ r) l.

Definition set_reg (ρ: regmap) (r: reg) (v: val) : regmap :=
  NatMap.add r v ρ.

Definition get_at (m: memory) (addr: val) : option val :=
  if (addr >=? 0)%Z
  then NatMap.find (Z.to_nat addr) m
  else None.

Definition set_at (m: memory) (addr: val) (v: val) : option memory :=
  if (addr >=? 0)%Z
  then
    let addr := Z.to_nat addr in
    if NatMap.mem addr m
    then Some (NatMap.add addr v m)
    else None
  else None.

(* Assert that instruction at [pc] in function [f] is [i] *)
Notation "f '@' pc 'is' i" :=
  (NatMap.find pc (fn_code f) = Some i) (at level 60, no associativity).

Definition eval_op (op: op) (args: list val) : option val :=
  match op, args with
  | Add, [v1; v2] => Some (v1 + v2)%Z
  | Sub, [v1; v2] => Some (v1 - v2)%Z
  | Mul, [v1; v2] => Some (v1 * v2)%Z
  | Move, [v] => Some v
  | LoadI v, [] => Some v
  | _, _ => None
  end.

Fixpoint init_regs (vl: list val) (rl: list reg) : regmap :=
  match rl, vl with
  | r :: rs, v :: vs => NatMap.add r v (init_regs vs rs)
  | _, _ => NatMap.empty _
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
    (v: val) (* return value for the call *)
.

Definition state : Type := list stackframe * pcstate * memory.

Definition find_fun (P: program) (s: sig) : option function :=
  List.find
    (fun f =>
       let sig := fn_sig f in
       let same_len :=
         Nat.eqb (List.length (in_regs sig)) (List.length (in_regs s)) in
       let same_name := String.eqb (name sig) (name s) in
       andb same_len same_name) P.

Reserved Notation "P '⊢' s '->>' t" (at level 60, right associativity).

Inductive step (P: program) : state -> state -> Prop :=
| exec_Inop: forall σ m ρ f pc pc',
  f@pc is <{ nop -> pc' }> ->
  P ⊢ (σ, State f pc ρ, m) ->> (σ, State f pc' ρ, m)

| exec_Iret: forall σ m ρ f pc r v,
  f@pc is <{ ret r }> ->
  get_reg ρ r = v ->
  P ⊢ (σ, State f pc ρ, m) ->> (σ, ReturnState v, m)

| exec_Iop: forall σ m ρ f pc op args dst pc' ρ' v,
  f@pc is <{ dst := @op args -> pc' }> ->
  eval_op op (get_regs ρ args) = Some v ->
  set_reg ρ dst v = ρ' ->
  P ⊢ (σ, State f pc ρ, m) ->> (σ, State f pc' ρ', m)

| exec_Iload: forall σ m ρ f pc dst src pc' ρ' addr v,
  f@pc is <{ dst := !src -> pc' }> ->
  get_reg ρ src = addr ->
  get_at m addr = Some v ->
  set_reg ρ dst v = ρ' ->
  P ⊢ (σ, State f pc ρ, m) ->> (σ, State f pc' ρ', m)

| exec_Istore: forall σ m ρ f pc dst src pc' m' addr v,
  f@pc is <{ !dst := src -> pc' }> ->
  get_reg ρ dst = addr ->
  get_reg ρ src = v ->
  set_at m addr v = Some m' ->
  P ⊢ (σ, State f pc ρ, m) ->> (σ, State f pc' ρ, m')

| exec_Icond: forall  σ m ρ f pc cond ifso ifnot v pc',
  f@pc is <{ if cond then goto ifso else goto ifnot }> ->
  get_reg ρ cond = v ->
  pc' = (if Z.eqb v 0 then ifso else ifnot) ->
  P ⊢ (σ, State f pc ρ, m) ->> (σ, State f pc' ρ, m)

| exec_Icall: forall σ m ρ f pc dst sig args pc' σ' fn,
  f@pc is <{ dst := @call sig args -> pc' }> ->
  find_fun P sig = Some fn ->
  Stackframe dst f pc' ρ :: σ = σ' ->
  P ⊢ (σ, State f pc ρ, m) ->> (σ', CallState fn (get_regs ρ args), m)

| exec_function: forall σ m ρ f args,
  init_regs args (in_regs f.(fn_sig)) = ρ ->
  P ⊢ (σ, CallState f args, m) ->> (σ, State f (fn_entrypoint f) ρ, m)

| exec_return: forall σ m ρ f pc dst v ρ',
  set_reg ρ dst v = ρ' ->
  P ⊢ (Stackframe dst f pc ρ :: σ, ReturnState v, m) ->> (σ, State f pc ρ', m)

where "P '⊢' s '->>' t" := (step P s t).

Definition steps (P: program) : state -> state -> Prop
  := clos_refl_trans state (step P).

Notation "P '⊢' s '->>*' t" :=
  (steps P s t) (at level 60, right associativity).

#[global]
Add Parametric Relation (P: program) : state (steps P)
  reflexivity proved by (rt_refl state (step P))
  transitivity proved by (rt_trans state (step P))
  as steps_rel.

Lemma inv_step : forall P s t,
  P ⊢ s ->>* t -> s = t ∨ ∃ s', P ⊢ s ->> s' ∧ P ⊢ s' ->>* t.
Proof.
  intros P s t Hred.
  apply clos_rt_rt1n_iff in Hred.
  destruct Hred as [ | s' t H Hred ].
  - auto.
  - apply clos_rt_rt1n_iff in Hred. right. now exists s'.
Qed.

Lemma lift_step P : ∀ σ s m σ' t m' Σ,
  P ⊢ (σ, s, m) ->> (σ', t, m') ->
  P ⊢ (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m').
Proof.
  intros ? ? ? ? ? ? ? H; inv H; econstructor; now eauto.
Qed.

Lemma unlift_step P : ∀ σ s m σ' t m' Σ,
  P ⊢ (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m') ->
  P ⊢ (σ, s, m) ->> (σ', t, m').
Proof.
  intros ? ? ? ? ? ? ? H; inv H;
    rewrite ? app_comm_cons in *;
    eassert _ by (eapply app_inv_tail; eassumption);
    subst; econstructor; now eauto.
Qed.

Theorem step_callstack P : ∀ σ s m σ' t m' Σ,
  P ⊢ (σ, s, m) ->> (σ', t, m') <->
  P ⊢ (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m').
Proof. split. 1: apply lift_step. apply unlift_step. Qed.

Theorem lift_steps P : ∀ σ s m σ' t m' Σ,
  P ⊢ (σ, s, m) ->>* (σ', t, m') ->
  P ⊢ (σ ++ Σ, s, m) ->>* (σ' ++ Σ, t, m').
Proof.
  intros σ s m σ' t m' Σ Hred.
  remember (σ, s, m) as x eqn:Hx.
  remember (σ', t, m') as y eqn:Hy.
  revert σ s m Hx σ' t m' Hy.
  apply clos_rt_rt1n_iff in Hred.
  induction Hred as [ y | x y z Hstep Hred IH ].
  - intros ? ? ? -> ? ? ? H. inv H. reflexivity.
  - intros ? ? ? -> ? ? ? H. destruct y as [[] ?].
    etransitivity.
    + apply rt_step; apply lift_step; eassumption.
    + eauto.
Qed.

Lemma unfold_call P fn : ∀ res f pc ρ args m σ t m',
  P ⊢ ([Stackframe res f pc ρ], CallState fn args, m) ->>* (σ, t, m') ->
  (∃ σ',
      σ = σ' ++ [Stackframe res f pc ρ]
      ∧ P ⊢ ([], CallState fn args, m) ->>* (σ', t, m'))
  ∨
    (∃ v m'',
        P ⊢ ([], CallState fn args, m) ->>* ([], ReturnState v, m'')
        ∧ P ⊢ ([], State f pc (set_reg ρ res v), m'') ->>* (σ, t, m')
    ).
Proof.
  intros res f pc ρ args m σ t m' H.
  remember [Stackframe res f pc ρ] as l.
  remember (l, CallState fn args, m) as s1 eqn:Hs1.
  remember (σ, t, m') as s2 eqn:Hs2.
  revert s2 H σ t m' Hs2.
  induction 1 as [ | [[σ1 t1] m1] z Hred IH Hstep]
                   using clos_refl_trans_ind_left;
    intros σ t m' ->.
  - inv Hs1. left. now exists [].
  - destruct (IH _ _ _ (eq_refl _ )) as
      [(σ' & -> & Hlift) | (v & m'' & Hcall & Hrest)]; clear IH.
    + inv Hstep;
        try (left; eexists; split;
             [ rewrite ? app_comm_cons; reflexivity
             | eapply rt_trans; [ apply Hlift | apply rt_step];
               econstructor; now eauto
             ]
          ).
      destruct σ'; inv H.
      * right. repeat eexists; now eauto.
      * left. eexists. split.
        -- reflexivity.
        -- eapply rt_trans; [apply Hlift | apply rt_step];
             econstructor; now eauto.
    + inversion Hstep; subst; right; repeat eexists;
        now eauto ||
          (eapply rt_trans; [apply Hrest | apply rt_step];
           econstructor; now eauto).
Qed.
