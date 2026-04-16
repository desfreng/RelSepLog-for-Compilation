From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.

From stdpp Require Import gmap.
From stdpp Require Import list.

Definition ident : Type := string.
Definition val : Type := Z.

Definition node := nat.
Definition loc := positive.
Definition reg := nat.

Inductive op : Type :=
| Add
| Sub
| Mul
| Move
| LoadI (v: val).

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
    fn_regs_no_dup : NoDup fn_regs;
  }.

Record program := {
    prog_func: list function;
    prog_main: ident;
    prog_wf: ∃ f, In f prog_func ∧ fn_name f = prog_main;
}.

Definition find_fun (P: program) (s: ident) : option function :=
  List.find (fun f => (fn_name f =? s)%string) (prog_func P).

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
