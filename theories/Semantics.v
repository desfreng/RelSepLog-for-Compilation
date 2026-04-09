From Stdlib Require Import Utf8.

From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.

From stdpp Require Import gmap.
From stdpp Require Import relations.
From stdpp Require Import tactics.

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

Definition get_reg (r: reg) (ρ: regmap) : val :=
  match ρ !! r with
  | Some v => v
  | None => 0%Z (* Dummy val *)
  end.

Definition get_regs (l: list reg) (ρ: regmap) : list val :=
  map (fun r => get_reg r ρ) l.

Definition set_reg (r: reg) (v: val) (ρ: regmap) : regmap := <[r := v]>ρ.

Definition get_at (addr: val) (m: memory) : option val :=
  match val_to_loc addr with
  | Some loc => m !! loc
  | None => None
  end.

Definition update_at (addr: val) (f: val -> val) (m: memory) : option memory
  := match val_to_loc addr with
     | Some loc =>
         match m !! loc with
         | Some old => Some (<[loc := f old]>m)
         | None => None
         end
     | None => None
     end.

Definition set_at (addr: val) (v: val) (m: memory) : option memory :=
  update_at addr (fun _ => v) m.

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
  get_reg r ρ = v ->
  P |- (σ, State f pc ρ, m) ->> (σ, ReturnState v, m)

| exec_Iop: forall σ m ρ f pc op args dst pc' ρ' v,
  f@pc is <{ dst := @op args -> pc' }> ->
  eval_op op (get_regs args ρ) = Some v ->
  set_reg dst v ρ = ρ' ->
  P |- (σ, State f pc ρ, m) ->> (σ, State f pc' ρ', m)

| exec_Iload: forall σ m ρ f pc dst src pc' ρ' addr v,
  f@pc is <{ dst := !src -> pc' }> ->
  get_reg src ρ = addr ->
  get_at addr m = Some v ->
  set_reg dst v ρ = ρ' ->
  P |- (σ, State f pc ρ, m) ->> (σ, State f pc' ρ', m)

| exec_Istore: forall σ m ρ f pc dst src pc' m' addr v,
  f@pc is <{ !dst := src -> pc' }> ->
  get_reg dst ρ = addr ->
  get_reg src ρ = v ->
  set_at addr v m = Some m' ->
  P |- (σ, State f pc ρ, m) ->> (σ, State f pc' ρ, m')

| exec_Icond: forall  σ m ρ f pc cond ifso ifnot v pc',
  f@pc is <{ if cond then goto ifso else goto ifnot }> ->
  get_reg cond ρ = v ->
  pc' = (if Z.eqb v 0 then ifso else ifnot) ->
  P |- (σ, State f pc ρ, m) ->> (σ, State f pc' ρ, m)

| exec_Icall: forall σ m ρ f pc dst sig args pc' σ' fn,
  f@pc is <{ dst := @call sig args -> pc' }> ->
  find_fun P sig = Some fn ->
  Stackframe dst f pc' ρ :: σ = σ' ->
  P |- (σ, State f pc ρ, m) ->> (σ', CallState fn (get_regs args ρ), m)

| exec_function: forall σ m ρ f args,
  length args = length (fn_regs f) ->
  init_regs args (fn_regs f) = ρ ->
  P |- (σ, CallState f args, m) ->> (σ, State f (fn_entrypoint f) ρ, m)

| exec_return: forall σ m ρ f pc dst v ρ',
  set_reg dst v ρ = ρ' ->
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
        ∧ P |- ([], State f pc (set_reg res v ρ), m'') -{m2}> (σ, t, m')
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
    + inv Hstep as [ | | | | | | | | ? ? ? ? ? ? v ? ? Hσ];
        try (left; eexists; split;
             [ rewrite ? app_comm_cons; reflexivity
             | eapply nsteps_r; [ now apply Hlift | econstructor; now eauto]
             ]
          ).
      destruct σ'; inv Hσ.
      * right. exists n, 0, v, m'. repeat split; eauto. constructor.
      * left. eexists. split.
        -- reflexivity.
        -- eapply nsteps_r; [ now apply Hlift | econstructor; now eauto].
    + inversion Hstep; subst; right; (exists m1, (S m2), v, m''); repeat split;
        now eauto || (eapply nsteps_r;
                      [ now apply Hrest | econstructor; now eauto]).
Qed.

Lemma get_regs_insert : ∀ regs r v ρ,
  r ∉ regs ->
  get_regs regs (<[r := v]> ρ) = get_regs regs ρ.
Proof.
  intros regs r v ρ.
  induction regs as [|r' regs' IH]; intros Hnotin; [reflexivity |].
  simpl. f_equal.
  - unfold get_reg. rewrite (lookup_insert_ne ρ); set_solver.
  - apply IH. set_solver.
Qed.

Lemma get_regs_init_regs : ∀ regs args,
  NoDup regs ->
  length args = length regs ->
  get_regs regs (init_regs args regs) = args.
Proof.
  intros regs args Hnodup.
  revert args.
  induction Hnodup as [|r regs Hnotin Hnodup IH]; intros args Hlen.
  - destruct args; [reflexivity | discriminate Hlen].
  - destruct args as [|v args]; [discriminate Hlen |].
    simpl in Hlen. injection Hlen as Hlen'.
    simpl. f_equal.
    + unfold get_reg. now rewrite (lookup_insert_eq (init_regs args regs)).
    + rewrite get_regs_insert by exact Hnotin.
      apply IH. exact Hlen'.
Qed.

Lemma get_reg_set_reg_eq : ∀ r v ρ,
  get_reg r (set_reg r v ρ) = v.
Proof.
  intros r v ρ.
  unfold get_reg, set_reg.
  now rewrite (lookup_insert_eq ρ).
Qed.

Lemma get_reg_set_reg_neq : ∀ r r' v ρ,
  r ≠ r' -> get_reg r (set_reg r' v ρ) = get_reg r ρ.
Proof.
  intros r r' v ρ Hneq.
  unfold get_reg, set_reg.
  now rewrite (lookup_insert_ne ρ).
Qed.

Tactic Notation "simpl_reg" "by" tactic3(tac) :=
  repeat match goal with
    | _ => progress tac
    | |- context[get_reg _ (set_reg _ _ _)] =>
        (rewrite get_reg_set_reg_neq by tac)
        || (rewrite get_reg_set_reg_eq by tac)
    end.

Tactic Notation "simpl_reg" := simpl_reg by (f_equal; lia).
