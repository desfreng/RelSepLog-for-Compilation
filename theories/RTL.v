From Stdlib Require Import Strings.String.
From Stdlib Require Import FSets.FMapPositive.
From Stdlib Require Import PArith.PArith.

Definition ident := string.
Definition node := positive.
Definition reg := positive.
Definition val := Z.

Inductive op : Type := Add | Sub | Mul | Move.

Structure sig := {
    name: ident;
    in_regs: list reg;
  }.

Inductive instr : Type :=
| Inop: node -> instr
    (** No operation -- just branch to the successor. *)
| Iop: op -> list reg -> reg -> node -> instr
    (** [Iop op args dest succ] performs the arithmetic operation [op]
        over the values of registers [args], stores the result in [dest],
        and branches to [succ]. *)
| IloadI : val -> reg -> node -> instr
    (** [IloadI val dest succ] set the register [dest] to the immediate value
        [val]. It then branch to [succ]. *)
| Iload: reg -> reg -> node -> instr
    (** [Iload addr dest succ] loads the value at [addr] into [dest],
        and branches to [succ]. *)
| Istore: reg -> reg -> node -> instr
    (** [Istore addr src succ] stores the value of register
        [src] at memory address [src], then branches to [succ]. *)
| Icall: sig -> list reg -> reg -> node -> instr
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
Definition code := PositiveMap.t instr.

(** A [function] includes its signature, an entry node, and its code. *)
Record function := {
    fn_sig : sig;
    fn_entrypoint : node;
    fn_code : code;
}.

(** A [program] is a list of functions. *)
Definition program := list function.
