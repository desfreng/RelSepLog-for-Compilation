From Corelib Require Import Setoid.

From Stdlib Require Import Utf8.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import FSets.FMapPositive.
From Stdlib Require Import PArith.PArith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.

From RSL Require Import RTL.
From RSL Require Import Notations.

Import RTLNotations.
Import ListNotations.

(* [regval] is a mapping from registers to a value *)
Definition regval : Type := PositiveMap.t val.

(* [memory] is a mapping from location to a value *)
Definition memory : Type := PositiveMap.t val.

(* A [pstate] is tuple of [(regval, memory)] *)
Structure pstate : Type :=
  { regs : regval;
    mem : memory
  }.

Definition get_val (σ: pstate) (r: reg) : val :=
  match PositiveMap.find r (regs σ) with
  | Some v => v
  | None => 0%Z (* Dummy val *)
  end.

Definition get_vals (σ: pstate) (l: list reg) : list val :=
  map (fun r => get_val σ r) l.

Definition set_val (σ: pstate) (r: reg) (v: val) : pstate :=
  {|
    regs := PositiveMap.add r v (regs σ);
    mem := mem σ
  |}.

Definition get_at (σ: pstate) (addr: val) : option val :=
  PositiveMap.find (Z.to_pos addr) (mem σ).

Definition set_at (σ: pstate) (addr: val) (v: val) : pstate :=
  {|
    regs := regs σ;
    mem := PositiveMap.add (Z.to_pos addr) v (mem σ)
  |}.

(* Read register *)
Notation "σ '[|' r '|]'" :=
  (get_val σ r) (at level 9, no associativity).

(* Read multiples registers *)
Notation "σ '[[|' l '|]]'" :=
  (get_vals σ l) (at level 9, no associativity).

(* Set register *)
Notation "σ '[|' r '<-' v '|]'" :=
  (set_val σ r v) (at level 9, no associativity).

(* Read at address *)
Notation "σ '[|' '@' k '|]'" :=
  (get_at σ k) (at level 9, no associativity).

(* Set at address register *)
Notation "σ '[|' '@' r '<-' v '|]'" :=
  (set_at σ r v) (at level 9, no associativity).

(* Assert that instruction at [pc] in function [f] is [i] *)
Notation "pc '|->' i 'in' m" :=
  (PositiveMap.find pc (fn_code m) = Some i) (at level 60, no associativity).

Ltac pc_inj :=
  match goal with
  | [ H1: ?pc |-> ?x in ?f, H2: ?pc |-> ?y in ?f |- _ ] =>
      let H := fresh in
      assert (H: x = y) by congruence; inversion H; subst; clear H2 H
  end.

Definition eval_op (op: op) (args: list val) : option val :=
  match op, args with
  | Add, [v1; v2] => Some (v1 + v2)%Z
  | Sub, [v1; v2] => Some (v1 - v2)%Z
  | Mul, [v1; v2] => Some (v1 * v2)%Z
  | Move, [v] => Some v
  | _, _ => None
  end.

Fixpoint init_regs (vl: list val) (rl: list reg) : regval :=
  match rl, vl with
  | r :: rs, v :: vs => PositiveMap.add r v (init_regs vs rs)
  | _, _ => PositiveMap.empty _
  end.

Definition init_state (m: memory) (vl: list val) (rl: list reg) : pstate :=
  {|
    regs := init_regs vl rl;
    mem := m
  |}.

Inductive stackframe : Type :=
| Stackframe
    (res: reg) (* where to store the result *)
    (f: function) (* calling function *)
    (pc: node) (* program point in caller function *)
    (rgs: regval) (* state in caller function *)
.

Inductive state : Type :=
| State
    (ρ: list stackframe) (* call stack *)
    (f: function) (* current function *)
    (pc: node) (* current program point in c *)
    (σ: pstate) (* register state *)

| CallState
    (ρ: list stackframe) (* call stack *)
    (f: function) (* function to call *)
    (args: list val) (* arguments to the call *)
    (mem: memory) (* memory state *)

| ReturnState
    (ρ: list stackframe) (* call stack *)
    (v: val) (* return value for the call *)
    (mem: memory) (* memory state *)
.

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
| exec_Inop: forall ρ f pc σ pc',
  pc |-> <{ nop -> pc' }> in f ->
  P ⊢ State ρ f pc σ ->> State ρ f pc' σ

| exec_Iret: forall ρ f pc σ r,
  pc |-> <{ ret r }> in f ->
  P ⊢ State ρ f pc σ ->> ReturnState ρ σ[|r|] (mem σ)

| exec_Iop: forall ρ f pc σ op args dst pc' v,
  pc |-> <{ dst := @op args -> pc' }> in f ->
  eval_op op σ[[| args |]] = Some v ->
  P ⊢ State ρ f pc σ ->> State ρ f pc' σ[|dst <- v|]

| exec_Iloadi: forall ρ f pc σ dst pc' v,
  pc |-> <{ dst := #v -> pc' }> in f ->
  P ⊢ State ρ f pc σ ->> State ρ f pc' σ[|dst <- v|]

| exec_Iload: forall ρ f pc σ dst src pc' a v,
  pc |-> <{ dst := !src -> pc' }> in f ->
  σ[|src|] = a ->
  σ[|@a|] = Some v ->
  P ⊢ State ρ f pc σ ->> State ρ f pc' σ[|dst <- v|]

| exec_Istore: forall ρ f pc σ addr src pc' a v,
  pc |-> <{ !addr := src -> pc' }> in f ->
  σ[|addr|] = a ->
  σ[|src|] = v ->
  P ⊢ State ρ f pc σ ->> State ρ f pc' σ[| @a <- v|]

| exec_Icall: forall ρ f pc σ dst sig args pc' fd,
  pc |-> <{ dst := @call sig args -> pc' }> in f ->
  find_fun P sig = Some fd ->
  P ⊢ State ρ f pc σ ->>
    CallState (Stackframe dst f pc' (regs σ) :: ρ) fd σ[[|args|]] (mem σ)

| exec_Icond: forall ρ f pc σ cond ifso ifnot v pc',
  pc |-> <{ if cond then goto ifso else goto ifnot }> in f ->
  σ[|cond|] = v ->
  pc' = (if Z.eqb v 0 then ifso else ifnot) ->
  P ⊢ State ρ f pc σ ->> State ρ f pc' σ

| exec_function: forall ρ f args mem,
  P ⊢ CallState ρ f args mem ->>
        State ρ f (fn_entrypoint f) (init_state mem args (in_regs f.(fn_sig)))

| exec_return: forall dst f pc rgs ρ v mem,
  P ⊢ ReturnState (Stackframe dst f pc rgs :: ρ) v mem ->>
    State ρ f pc (Build_pstate rgs mem)[|dst <- v|]

where "P '⊢' s '->>' t" := (step P s t).


Lemma exec_Inop' P : forall ρ f pc σ pc' s1 s2,
  pc |-> <{ nop -> pc' }> in f ->
  s1 = State ρ f pc σ ->
  s2 = State ρ f pc' σ ->
  P ⊢ s1 ->> s2.
Proof.
  intros; subst; now apply exec_Inop.
Qed.

Lemma exec_Iret' P : forall ρ f pc σ r v m,
  pc |-> <{ ret r }> in f ->
  σ [|r|] = v ->
  m = mem σ ->
  P ⊢ State ρ f pc σ ->> ReturnState ρ v m.
Proof.
  intros; subst; now apply exec_Iret.
Qed.

Section RTC.
  Context {A: Type} (R: A -> A -> Prop).

  Inductive rtc : A -> A -> Prop :=
  | rtc_refl : forall x, rtc x x
  | rtc_incl : forall x y, R x y -> rtc x y
  | rtc_trans : forall x y z, rtc x y -> rtc y z -> rtc x z.

  #[export] Instance rtx_Reflexive: Reflexive rtc := rtc_refl.
  #[export] Instance rtx_Transitive: Transitive rtc := rtc_trans.

  Lemma rtc_inv_step : forall x y,
    rtc x y ->
    x = y ∨ ∃ x', R x x' ∧ rtc x' y.
  Proof.
    intros x y H. induction H as [x | x y H | x y z H1 IH1 H2 IH2].
    - left; reflexivity.
    - right; eexists; split; eassumption || constructor.
    - destruct IH1 as [ -> | (x' & HR & Hrtc)].
      + assumption.
      + right; eexists; split.
        * eassumption.
        * eapply rtc_trans; eassumption.
  Qed.
End RTC.

Notation "P '⊢' s '->>*' t" :=
  (rtc (step P) s t) (at level 60, right associativity).

Definition f : function :=
  {|
    fn_sig :=
      {|
        name := "main"%string;
        in_regs := [3%positive]
      |};
    fn_entrypoint := 1%positive;
    fn_code :=
      <{{
          1: $1 := #1 -> 2;
          2: $2 := #(-5) -> 3;
          3: if $2 then goto 6 else goto 4;
          4: $3 := $1 + $3 -> 5;
          5: $2 := $1 + $2 -> 3;
          6: ret $3;
      }}>
  |}.

Ltac mysimp := unfold set_val, get_val; cbn -[Z.add Z.mul Z.sub].

Goal forall P ρ m v,
  P ⊢ CallState ρ f [v] m ->>* ReturnState ρ (v + 5)%Z m.
Proof.
  intros.

  eapply rtc_trans. apply rtc_incl; eapply exec_function; reflexivity. mysimp.
  unfold init_state, init_regs.

  eapply rtc_trans. apply rtc_incl; eapply exec_Iloadi; reflexivity. mysimp.
  eapply rtc_trans. apply rtc_incl; eapply exec_Iloadi; reflexivity. mysimp.

  eapply rtc_trans. apply rtc_incl; eapply exec_Icond; reflexivity. mysimp.
  eapply rtc_trans. apply rtc_incl; eapply exec_Iop; reflexivity. mysimp.
  eapply rtc_trans. apply rtc_incl; eapply exec_Iop; reflexivity. mysimp.

  eapply rtc_trans. apply rtc_incl; eapply exec_Icond; reflexivity. mysimp.
  eapply rtc_trans. apply rtc_incl; eapply exec_Iop; reflexivity. mysimp.
  eapply rtc_trans. apply rtc_incl; eapply exec_Iop; reflexivity. mysimp.

  eapply rtc_trans. apply rtc_incl; eapply exec_Icond; reflexivity. mysimp.
  eapply rtc_trans. apply rtc_incl; eapply exec_Iop; reflexivity. mysimp.
  eapply rtc_trans. apply rtc_incl; eapply exec_Iop; reflexivity. mysimp.

  eapply rtc_trans. apply rtc_incl; eapply exec_Icond; reflexivity. mysimp.
  eapply rtc_trans. apply rtc_incl; eapply exec_Iop; reflexivity. mysimp.
  eapply rtc_trans. apply rtc_incl; eapply exec_Iop; reflexivity. mysimp.

  eapply rtc_trans. apply rtc_incl; eapply exec_Icond; reflexivity. mysimp.
  eapply rtc_trans. apply rtc_incl; eapply exec_Iop; reflexivity. mysimp.
  eapply rtc_trans. apply rtc_incl; eapply exec_Iop; reflexivity. mysimp.

  eapply rtc_trans. apply rtc_incl; eapply exec_Icond; reflexivity. mysimp.

  apply rtc_incl. eapply exec_Iret'; try reflexivity.
  mysimp. lia.
Qed.

Section WP.
  Variable P : program.

  Definition postcondition : Type := val -> memory -> Prop.

  Definition final (Q: postcondition) (s: state) : Prop :=
    match s with
    | ReturnState ρ v m => Q v m
    | _ => False
    end.

  Definition safe (Q: postcondition) (s: state) : Prop :=
    ∀ s', P ⊢ s ->>* s' -> final Q s' ∨ ∃ s'', P ⊢ s' ->> s''.

  Definition wp (f: function) (pc: node) (Q: postcondition) :=
    fun σ => safe Q (State [] f pc σ).

  Lemma wp_ret f pc Q : forall v,
    pc |-> <{ ret v }> in f ->
    ∀ σ, Q σ[|v|] (mem σ) -> wp f pc Q σ.
  Proof.
    intros v H σ.
    unfold wp, safe.
    intros Hwp s' Hred.
    destruct (rtc_inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc )].
    - right. eexists. eapply exec_Iret'; eassumption || reflexivity.
    - inversion Hreds; subst; try congruence.
      destruct (rtc_inv_step _ _ _ Hrtc) as [ <- | (? & Hwhat & ? )].
      + pc_inj. auto.
      + inversion Hwhat.
  Qed.

  Lemma wp_nop f pc Q : forall pc',
    pc |-> <{ nop -> pc' }> in f ->
    ∀ σ, wp f pc' Q σ -> wp f pc Q σ.
  Proof.
    intros pc' H σ.
    unfold wp, safe.
    intros Hwp s' Hred.
    destruct (rtc_inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc )].
    - right. eexists. eapply exec_Inop'; eassumption || reflexivity.
    - apply Hwp; inversion Hreds; subst; pc_inj; congruence.
  Qed.

  Lemma wp_loadi f pc Q : forall dst v pc',
    pc |-> <{ dst := #v -> pc' }> in f ->
    ∀ σ, wp f pc' Q σ[|dst <- v|] ->
         wp f pc Q σ.
  Proof.
    intros dst v pc' H σ.
    unfold wp, safe.
    intros Hwp s' Hred.
    destruct (rtc_inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc)].
    - right. eexists. eapply exec_Iloadi; eassumption || reflexivity.
    - apply Hwp; inversion Hreds; subst; pc_inj; congruence.
  Qed.

  Lemma wp_op f pc Q : forall dst op args pc',
    pc |-> <{ dst := @op args -> pc' }> in f ->
    ∀ σ v,
      eval_op op σ[[|args|]] = Some v ->
      wp f pc' Q σ[|dst <- v|] ->
      wp f pc Q σ.
  Proof.
    intros dst op args pc' H σ v Heval.
    unfold wp, safe.
    intros Hwp s' Hred.
    destruct (rtc_inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc)].
    - right. eexists. eapply exec_Iop; eassumption || reflexivity.
    - apply Hwp; inversion Hreds; subst; pc_inj; congruence.
  Qed.

  Lemma wp_load f pc Q : forall dst src pc',
    pc |-> <{ dst := !src -> pc' }> in f ->
    ∀ σ v,
      σ[|@(σ[|src|])|] = Some v ->
      wp f pc' Q σ[|dst <- v|] ->
      wp f pc Q σ.
  Proof.
    intros dst src pc' H σ v Hmem.
    unfold wp, safe.
    intros Hwp s' Hred.
    destruct (rtc_inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc)].
    - right. eexists. eapply exec_Iload; eassumption || reflexivity.
    - apply Hwp; inversion Hreds; subst; pc_inj; congruence.
  Qed.

  Lemma wp_store f pc Q : forall addr src pc',
    pc |-> <{ !addr := src -> pc' }> in f ->
    ∀ σ, wp f pc' Q σ[|@(σ[|addr|]) <- σ[|src|]|] ->
         wp f pc Q σ.
  Proof.
    intros addr src pc' H σ.
    unfold wp, safe.
    intros Hwp s' Hred.
    destruct (rtc_inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc)].
    - right. eexists. eapply exec_Istore; eassumption || reflexivity.
    - apply Hwp; inversion Hreds; subst; pc_inj; congruence.
  Qed.

  Lemma wp_cond f pc Q : forall cond ifso ifnot,
    pc |-> <{ if cond then goto ifso else goto ifnot }> in f ->
    ∀ σ, wp f (if Z.eqb σ[|cond|] 0 then ifso else ifnot) Q σ ->
         wp f pc Q σ.
  Proof.
    intros cond ifso ifnot H σ.
    unfold wp, safe.
    intros Hwp s' Hred.
    destruct (rtc_inv_step _ _ _ Hred) as [ <- | (ss & Hreds & Hrtc)].
    - right. eexists. eapply exec_Icond; eassumption || reflexivity.
    - apply Hwp; inversion Hreds; subst; pc_inj; congruence.
  Qed.

End WP.
