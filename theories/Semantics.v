From Stdlib Require Import Utf8.

From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.

From stdpp Require Import gmap.
From stdpp Require Import relations.

From RSL Require Import Tactics.
From RSL Require Import RTL.
From RSL Require Import Notations.

Import RTLNotations.
Import ListNotations.

(* Set Mangle Names. *)

(* [regmap] is a mapping from registers to a value *)
Definition regmap : Type := gmap reg val.

(* [memory] is a mapping from location to a value *)
Definition memory : Type := gmap loc val.

Definition val_to_loc (v: val) : option loc :=
  if (v >=? 1)%Z
  then Some (Z.to_pos v)
  else None.

Definition get_reg (ρ: regmap) (r: reg) : val :=
  match ρ !! r with
  | Some v => v
  | None => 0%Z (* Dummy val *)
  end.

Definition get_regs (ρ: regmap) (l: list reg) : list val :=
  map (fun r => get_reg ρ r) l.

Definition set_reg (ρ: regmap) (r: reg) (v: val) : regmap := <[r := v]>ρ.

Definition get_at (m: memory) (addr: val) : option val :=
  match val_to_loc addr with
  | Some loc => m !! loc
  | None => None
  end.

Definition update_at (m: memory) (addr: val) (f: val -> val) : option memory
  := match val_to_loc addr with
     | Some loc =>
         match m !! loc with
         | Some old => Some (<[loc := f old]>m)
         | None => None
         end
     | None => None
     end.

Definition set_at (m: memory) (addr: val) (v: val) : option memory :=
  update_at m addr (fun _ => v).

(* Assert that instruction at [pc] in function [f] is [i] *)
Notation "f '@' pc 'is' i" :=
  ((fn_code f)!!pc = Some i) (at level 60, no associativity).

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
    (v: val) (* return value for the call *)
.

Definition state : Type := list stackframe * pcstate * memory.

Reserved Notation "P '|-' s '->>' t" (at level 60, right associativity).

Inductive step (P: program) : state -> state -> Prop :=
| exec_Inop: forall σ m ρ f pc pc',
  f@pc is <{ nop -> pc' }> ->
  P |- (σ, State f pc ρ, m) ->> (σ, State f pc' ρ, m)

| exec_Iret: forall σ m ρ f pc r v,
  f@pc is <{ ret r }> ->
  get_reg ρ r = v ->
  P |- (σ, State f pc ρ, m) ->> (σ, ReturnState v, m)

| exec_Iop: forall σ m ρ f pc op args dst pc' ρ' v,
  f@pc is <{ dst := @op args -> pc' }> ->
  eval_op op (get_regs ρ args) = Some v ->
  set_reg ρ dst v = ρ' ->
  P |- (σ, State f pc ρ, m) ->> (σ, State f pc' ρ', m)

| exec_Iload: forall σ m ρ f pc dst src pc' ρ' addr v,
  f@pc is <{ dst := !src -> pc' }> ->
  get_reg ρ src = addr ->
  get_at m addr = Some v ->
  set_reg ρ dst v = ρ' ->
  P |- (σ, State f pc ρ, m) ->> (σ, State f pc' ρ', m)

| exec_Istore: forall σ m ρ f pc dst src pc' m' addr v,
  f@pc is <{ !dst := src -> pc' }> ->
  get_reg ρ dst = addr ->
  get_reg ρ src = v ->
  set_at m addr v = Some m' ->
  P |- (σ, State f pc ρ, m) ->> (σ, State f pc' ρ, m')

| exec_Icond: forall  σ m ρ f pc cond ifso ifnot v pc',
  f@pc is <{ if cond then goto ifso else goto ifnot }> ->
  get_reg ρ cond = v ->
  pc' = (if Z.eqb v 0 then ifso else ifnot) ->
  P |- (σ, State f pc ρ, m) ->> (σ, State f pc' ρ, m)

| exec_Icall: forall σ m ρ f pc dst sig args pc' σ' fn,
  f@pc is <{ dst := @call sig args -> pc' }> ->
  find_fun P sig = Some fn ->
  Stackframe dst f pc' ρ :: σ = σ' ->
  P |- (σ, State f pc ρ, m) ->> (σ', CallState fn (get_regs ρ args), m)

| exec_function: forall σ m ρ f args,
  init_regs args (in_regs f.(fn_sig)) = ρ ->
  P |- (σ, CallState f args, m) ->> (σ, State f (fn_entrypoint f) ρ, m)

| exec_return: forall σ m ρ f pc dst v ρ',
  set_reg ρ dst v = ρ' ->
  P |- (Stackframe dst f pc ρ :: σ, ReturnState v, m) ->> (σ, State f pc ρ', m)

where "P '|-' s '->>' t" := (step P s t).

Notation "P '|-' s '->>*' t" :=
  (rtc (step P) s t)  (at level 60, right associativity).

Notation "P '|-' s '-{' n '}>' t" :=
  (nsteps (step P) n s t)  (at level 60, right associativity).

Lemma nsteps_inv_l {A : Type} {R : relation A} :
  ∀ n x z, nsteps R (S n) x z → ∃ y : A, R x y ∧ nsteps R n y z.
Proof. intros n x z H; inv H; eexists; eauto. Qed.

Lemma ret_no_step P : ∀ v m t,
  P |- ([], ReturnState v, m) ->>* t ->
  t = ([], ReturnState v, m).
Proof.
  intros v m t H.
  destruct (rtc_inv _ _ H) as [-> | (y & Hstep & _)].
  - easy.
  - inv Hstep.
Qed.

Lemma ret_no_nsteps P : ∀ n v m t,
  P |- ([], ReturnState v, m) -{n}> t ->
  t = ([], ReturnState v, m) ∧ n = 0.
Proof.
  intros [] v m t H.
  - now inv H.
  - destruct (nsteps_inv_l _ _ _ H) as (y & Hstep & _).
    inv Hstep.
Qed.

Lemma lift_step P : ∀ σ s m σ' t m' Σ,
  P |- (σ, s, m) ->> (σ', t, m') ->
  P |- (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m').
Proof.
  intros ? ? ? ? ? ? ? H; inv H; econstructor; now eauto.
Qed.

Lemma unlift_step P : ∀ σ s m σ' t m' Σ,
  P |- (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m') ->
  P |- (σ, s, m) ->> (σ', t, m').
Proof.
  intros ? ? ? ? ? ? ? H; inv H;
    rewrite ? app_comm_cons in *;
    eassert _ by (eapply app_inv_tail; eassumption);
    subst; econstructor; now eauto.
Qed.

Theorem step_callstack P : ∀ σ s m σ' t m' Σ,
  P |- (σ, s, m) ->> (σ', t, m') <->
  P |- (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m').
Proof. split. 1: apply lift_step. apply unlift_step. Qed.

Theorem lift_steps P : ∀ σ s m σ' t m' Σ,
  P |- (σ, s, m) ->>* (σ', t, m') ->
  P |- (σ ++ Σ, s, m) ->>* (σ' ++ Σ, t, m').
Proof.
  intros σ s m σ' t m' Σ Hrtc.
  remember (σ, s, m) as x eqn:Hx.
  remember (σ', t, m') as y eqn:Hy.
  induction Hrtc as [ y | x y z H Hrtc IH]
    in σ, s, m, Hx, σ', t, m', Hy |- *.
  - subst. inv Hy. reflexivity.
  - subst. destruct y as [[] ?].
    etransitivity.
    + apply rtc_once. apply lift_step. eassumption.
    + eauto.
Qed.

Lemma unfold_call P fn : ∀ n res f pc ρ args m σ t m',
  P |- ([Stackframe res f pc ρ], CallState fn args, m) -{n}> (σ, t, m') ->
  (∃ σ',
      σ = σ' ++ [Stackframe res f pc ρ]
      ∧ P |- ([], CallState fn args, m) -{n}> (σ', t, m'))
  ∨
    (∃ m1 m2 v m'',
        n = 1 + m1 + m2
        ∧ P |- ([], CallState fn args, m) -{m1}> ([], ReturnState v, m'')
        ∧ P |- ([], State f pc (set_reg ρ res v), m'') -{m2}> (σ, t, m')
    ).
Proof.
  intros n.
  induction n as [ | n IH ];
    intros res f pc ρ args m σ t m' Hrtc.
  - inv Hrtc. left. exists []. split; auto. constructor.
  - apply nsteps_inv_r in Hrtc. destruct Hrtc as ([[] ?] & Hrtc & Hstep).
    apply IH in Hrtc.
    destruct Hrtc
      as [(σ' & -> & Hlift) | (m1 & m2 & v & m'' & Hn & Hcall & Hrest)].
    + inv Hstep;
        try (left; eexists; split;
             [ rewrite ? app_comm_cons; reflexivity
             | eapply nsteps_r; [ now apply Hlift | econstructor; now eauto]
             ]
          ).
      destruct σ'; inv H.
      * right. exists n, 0, v, m'. repeat split; eauto. constructor.
      * left. eexists. split.
        -- reflexivity.
        -- eapply nsteps_r; [ now apply Hlift | econstructor; now eauto].
    + inversion Hstep; subst; right; (exists m1, (S m2), v, m''); repeat split;
        now eauto || (eapply nsteps_r;
                      [ now apply Hrest | econstructor; now eauto]).
Qed.
