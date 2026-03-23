From Stdlib Require Import Lists.List.

Definition node := nat.

Definition reg := nat.

Inductive operation := Add | Mul | Move.

Inductive instruction: Type :=
| Inop: node -> instruction
    (** No operation -- just branch to the successor. *)
| Iop: operation -> list reg -> reg -> node -> instruction
    (** [Iop op args dest succ] performs the arithmetic operation [op]
        over the values of registers [args], stores the result in [dest],
        and branches to [succ]. *)
| Iload: reg -> reg -> node -> instruction
    (** [Iload addr dest succ] loads the value at [addr] into [dest],
        and branches to [succ]. *)
| Istore: reg -> reg -> node -> instruction
    (** [Istore addr src succ] stores the value of register
        [src] at memory address [src], then branches to [succ]. *)
| Icall: signature -> ident -> list reg -> reg -> node -> instruction
    (** [Icall sig fn args dest succ] invokes the function determined by
        [fn], giving it the values of registers [args] as arguments.
        It stores the return value in [dest] and branches to [succ]. *)
| Icond: reg -> node -> node -> instruction
    (** [Icond cond args ifso ifnot] evaluates the boolean condition
        [cond] over the values of registers [args].  If the condition
        is true, it transitions to [ifso].  If the condition is false,
        it transitions to [ifnot]. *)
| Ireturn: reg -> instruction.
    (** [Ireturn] terminates the execution of the current function
        (it has no successor). It returns the value of the given
        register. *)
