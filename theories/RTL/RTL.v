From RSL Require Import Prelude.

From RSL.Commons Require Export Memory RegisterBank NoDup.

From stdpp Require Import gmap.
From stdpp Require Import strings.

Definition node : Type := nat.
Definition ident : Type := string.

Variant op : Type :=
  | Add
  | Sub
  | Mul
  | Div
  | Move
  | ImmInt (v: Z)
  | ImmBool (v: bool)
  | Incr
  | Decr
  | EqZ.

Inductive rtl_instr : Type :=
    (** No operation -- just branch to the successor. *)
| Inop: node -> rtl_instr
    (** [Iop op args dest succ] performs the pure (not memory related)
        operation [op] over the values of registers [args],
        stores the result in [dest], and branches to [succ]. *)
| Iop: op -> list reg -> reg -> node -> rtl_instr
    (** [Irand dest succ] set the register [dest] to a random integer value,
        and branches to [succ]. *)
| Irand: reg -> node -> rtl_instr
    (** [Iload addr dest succ] loads the value at [addr] into [dest],
        and branches to [succ]. *)
| Iload: reg -> reg -> node -> rtl_instr
    (** [Istore addr src succ] stores the value of register
        [src] at memory address [src], then branches to [succ]. *)
| Istore: reg -> reg -> node -> rtl_instr
    (** [Ialloc dst succ] allocate a new memory cell and store the pointer into [dst],
        and branches to [succ]. *)
| Ialloc: reg -> node -> rtl_instr
    (** [Ifree addr] free the address stored in [addr],
        then branches to [succ]. *)
| Ifree: reg -> node -> rtl_instr
    (** [Icall sig args dest succ] invokes the function determined by
        [fn], giving it the values of registers [args] as arguments.
        It stores the return value in [dest] and branches to [succ]. *)
| Icall: ident -> list reg -> reg -> node -> rtl_instr
    (** [Icond cond args ifso ifnot] branch on the value in [cond].
        If the value in register [cond] is non zero, it transitions to [ifso].
        Otherwise it transitions to [ifnot]. *)
| Icond: reg -> node -> node -> rtl_instr
    (** [Ireturn reg] terminates the execution of the current function
        (it has no successor). It returns the value of the register [reg]. *)
| Ireturn: reg -> rtl_instr.

(** [code] is a finite map from nodes to rtl_instructions *)
Definition rtl_code := gmap node rtl_instr.

(** A [function] includes its signature, an entry node, and its code. *)
Record rtl_function := {
    rtl_fn_name: ident;
    rtl_fn_regs: list reg;
    rtl_fn_entrypoint : node;
    rtl_fn_code : rtl_code;
    rtl_fn_regs_no_dup : is_no_dup rtl_fn_regs = true;
  }.

Definition find_fun_in_list (L: list rtl_function) (s: ident) : option rtl_function :=
  snd <$> list_find (fun f => (rtl_fn_name f =? s)%string) L.

Record rtl_program := {
    prog_fun_list: list rtl_function;

    prog_main: ident;

    prog_fun_list_no_dup:
      is_no_dup (rtl_fn_name <$> prog_fun_list) = true;

    prog_main_exists:
      is_Some (find_fun_in_list prog_fun_list prog_main);
}.

Definition find_fun (P: rtl_program) (s: ident) : option rtl_function :=
  find_fun_in_list (prog_fun_list P) s.

Lemma rtl_fun_no_dup f : NoDup (rtl_fn_regs f).
Proof using Type. by apply is_no_dup_sound, rtl_fn_regs_no_dup. Qed.

(* Assert that rtl_instruction at [pc] in function [f] is [i] *)
Notation "f '@' pc 'is' i" :=
  ((rtl_fn_code f)!!pc = Some i) (at level 60, no associativity).

Definition eval_op (op: op) (args: list val) : option val :=
  match op, args with
  | Add, [VInt v1; VInt v2] => Some (VInt (v1 + v2)%Z)
  | Sub, [VInt v1; VInt v2] => Some (VInt (v1 - v2)%Z)
  | Mul, [VInt v1; VInt v2] => Some (VInt (v1 * v2)%Z)
  | Div, [VInt v1; VInt v2] =>
      if (v2 =? 0)%Z
      then None
      else Some (VInt (v1 / v2)%Z)
  | Move, [v] => Some v
  | ImmInt v, [] => Some (VInt v)
  | ImmBool b, [] => Some (VBool b)
  | Incr, [VInt v] => Some (VInt (v + 1)%Z)
  | Decr, [VInt v] => Some (VInt (v - 1)%Z)
  | EqZ, [VInt v] => Some (VBool (v =? 0)%Z)
  | _, _ => None
  end.
