From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.

From RSL Require Import NatMap.
From RSL Require Import RTL.

Import ListNotations.

Module RTLNotations.
  Declare Custom Entry rtl_code.
  Declare Custom Entry rtl_instr.
  Declare Custom Entry rtl_reg.
  Declare Custom Entry rtl_reg_list.
  Declare Custom Entry rtl_args.

  Notation "<{{ c }}>" :=
    c (c custom rtl_code at level 99,
       format "'[v ' '<{{' '//' c '//' '}}>' ']'").

  Notation "<{ c }>" :=
    c (c custom rtl_instr at level 99).

  (* Code Block Notations *)
  Notation "n ':' i ';'" :=
    (NatMap.add n i (NatMap.empty instr))
      (in custom rtl_code at level 0,
          n constr at level 0,
          i custom rtl_instr at level 0,
          format "'[ ' n ':'  i ';' ']'").

  Notation "n ':' i ';' rest" :=
    (NatMap.add n i rest)
      (in custom rtl_code at level 0,
          n constr at level 0,
          i custom rtl_instr at level 0,
          rest custom rtl_code at level 0,
          format "'[ ' n ':'  i ';' ']' '//' rest").

  Notation "'$' v" := (v) (in custom rtl_reg at level 0, v constr at level 0).
  Notation "x" := x (in custom rtl_reg at level 0, x ident).

  (* Instruction Notations *)

  (* Nop *)
  Notation "'nop' '->' next" :=
    (Inop next)
      (in custom rtl_instr at level 0, next constr at level 0).

  (* Operations *)
  Notation "dst ':=' '@' op src '->' next" :=
    (Iop op src dst next)
      (in custom rtl_instr at level 0,
          dst custom rtl_reg at level 0,
          op ident,
          src constr at level 0,
          next constr at level 0).

  (* LoadI *)
  Notation "dst ':=' '#' val '->' next" :=
    (Iop (LoadI val%Z) [] dst next)
      (in custom rtl_instr at level 0,
          dst custom rtl_reg at level 0,
          val constr at level 0,
          next constr at level 0).

  (* Move *)
  Notation "dst ':=' src '->' next" :=
    (Iop Move [src] dst next)
      (in custom rtl_instr at level 0,
          dst custom rtl_reg at level 0,
          src custom rtl_reg at level 0,
          next constr at level 0).

  (* Add *)
  Notation "dst ':=' src1 '+' src2 '->' next" :=
    (Iop Add [src1; src2] dst next)
      (in custom rtl_instr at level 0,
          dst custom rtl_reg at level 0,
          src1 custom rtl_reg at level 0,
          src2 custom rtl_reg at level 0,
          next constr at level 0).

  (* Mult *)
  Notation "dst ':=' src1 '*' src2 '->' next" :=
    (Iop Mul [src1; src2] dst next)
      (in custom rtl_instr at level 0,
          dst custom rtl_reg at level 0,
          src1 custom rtl_reg at level 0,
          src2 custom rtl_reg at level 0,
          next constr at level 0).

  (* Load *)
  Notation "dst ':=' '!' addr '->' next" :=
    (Iload addr dst next)
      (in custom rtl_instr at level 0,
          dst custom rtl_reg at level 0,
          addr constr at level 0,
          next constr at level 0).

  (* Store *)
  Notation "'!' addr ':=' src '->' next" :=
    (Istore addr src next)
      (in custom rtl_instr at level 0,
          addr constr at level 0,
          src custom rtl_reg at level 0,
          next constr at level 0).

  (* Call *)
  Notation "dst ':=' 'call' sig args '->' next" :=
    (Icall sig args dst next)
      (in custom rtl_instr at level 0,
          dst custom rtl_reg at level 0,
          sig constr at level 0,
          args custom rtl_args at level 0,
          next constr at level 0).

  (* Call *)
  Notation "dst ':=' '@call' sig args '->' next" :=
    (Icall sig args dst next)
      (in custom rtl_instr at level 0,
          dst custom rtl_reg at level 0,
          sig constr at level 0,
          args constr at level 0,
          next constr at level 0).

  (* Cond *)
  Notation "'if' cond 'then' 'goto' ifso 'else' 'goto' ifnot" :=
    (Icond cond ifso ifnot)
      (in custom rtl_instr at level 0,
          cond custom rtl_reg at level 0,
          ifso constr at level 0,
          ifnot constr at level 0).

  (* Return *)
  Notation "'ret' src" :=
    (Ireturn src)
      (in custom rtl_instr at level 0,
          src custom rtl_reg at level 0).

  (* Args list *)

  (* Non Empty Call *)
  Notation "'(' ')'" := [] (in custom rtl_args at level 0).
  Notation "'()'" := [] (in custom rtl_args at level 0).
  Notation "'(' args ')'" :=
    args (in custom rtl_args at level 0, args custom rtl_reg_list at level 0).

  Notation "'$' v" :=
    [v] (in custom rtl_reg_list at level 0, v constr at level 0).
  Notation "'$' v ',' rest" :=
    (v :: rest)
      (in custom rtl_reg_list at level 0,
          v constr at level 0,
          rest custom rtl_reg_list at level 0).

End RTLNotations.

Module Test.
  Import ListNotations.
  Import RTLNotations.

  Definition test_sig : sig :=
    {| name := "test"%string; in_regs := [1] |}.

  Definition my_code : code := <{{
          1: nop -> 2;
          2: $1 := #32 -> 3;
          3: $1 := $2 -> 4;
          4: $1 := $2 + $3 -> 5;
          5: $1 := $2 * $3 -> 6;
          6: $1 := !2 -> 7;
          7: !1 := $2 -> 8;
          8: if $1 then goto 9 else goto 9;
          9: ret $1;
      }}>.

  Definition my_code_2 (r: reg) (n: node) (v: val) (op: op): code := <{{
          (n): nop -> (n+1);
          (n+1): r := #v -> (n+2);
          (n+2): r := r -> (n+3);
          (n+3): r := @op [r; r] -> (n+4);
          (n+4): r := r + r -> (n+5);
          (n+5): r := r * r -> (n+6);
          (n+6): r := !r -> (n+7);
          (n+7): !r := r -> (n+8);
          (n+8): if r then goto (n+9) else goto (n+9);
          (n+9): ret r;
      }}>.
End Test.
