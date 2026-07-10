From RSL Require Import Prelude.

From RSL.Commons Require Export Memory RegisterBank NoDup.

From stdpp Require Import gmap.
From stdpp Require Import strings.

Definition node : Type := nat.
Definition ident : Type := string.

Inductive op : Type :=
| Add
| Sub
| Mul
| Div
| Move
| LoadI (v: val)
| Incr
| Decr.

Inductive instr : Type :=
| Inop: node -> instr
    (** No operation -- just branch to the successor. *)
| Iop: op -> list reg -> reg -> node -> instr
    (** [Iop op args dest succ] performs the pure (not memory related)
        operation [op] over the values of registers [args],
        stores the result in [dest], and branches to [succ]. *)
| Iload: reg -> reg -> node -> instr
    (** [Iload addr dest succ] loads the value at [addr] into [dest],
        and branches to [succ]. *)
| Istore: reg -> reg -> node -> instr
    (** [Istore addr src succ] stores the value of register
        [src] at memory address [src], then branches to [succ]. *)
| Icall: ident -> list reg -> reg -> node -> instr
    (** [Icall sig args dest succ] invokes the function determined by
        [fn], giving it the values of registers [args] as arguments.
        It stores the return value in [dest] and branches to [succ]. *)
| Icond: reg -> node -> node -> instr
    (** [Icond cond args ifso ifnot] branch on the value in [cond].
        If the value in register [cond] is non zero, it transitions to [ifso].
        Otherwise it transitions to [ifnot]. *)
| Ireturn: reg -> instr
    (** [Ireturn reg] terminates the execution of the current function
        (it has no successor). It returns the value of the register [reg]. *)
.

(** [code] is a finite map from nodes to instructions *)
Definition code := gmap node instr.

(** A [function] includes its signature, an entry node, and its code. *)
Record function := {
    fn_name: ident;
    fn_regs: list reg;
    fn_entrypoint : node;
    fn_code : code;
    fn_regs_no_dup : is_no_dup fn_regs = true;
  }.

Record program := {
    prog_func: list function;
    prog_main: function;
}.

Definition find_fun (P: program) (s: ident) : option function :=
  List.find (fun f => (fn_name f =? s)%string) (prog_func P).

(* Assert that instruction at [pc] in function [f] is [i] *)
Notation "f '@' pc 'is' i" :=
  ((fn_code f)!!pc = Some i) (at level 60, no associativity).

Definition eval_op (op: op) (args: list val) : option val :=
  match op, args with
  | Add, [v1; v2] => Some (v1 + v2)%Z
  | Sub, [v1; v2] => Some (v1 - v2)%Z
  | Mul, [v1; v2] => Some (v1 * v2)%Z
  | Div, [v1; v2] =>
      if (v2 =? 0)%Z
      then None
      else Some (v1 / v2)%Z
  | Move, [v] => Some v
  | LoadI v, [] => Some v
  | Incr, [v] => Some (v + 1)%Z
  | Decr, [v] => Some (v - 1)%Z
  | _, _ => None
  end.
