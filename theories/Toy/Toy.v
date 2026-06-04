From RSL Require Import Prelude.

From RSL Require Export Commons.RegisterBank.

From stdpp Require Import strings.

Variant texpr : Type :=
| EReg (r: reg)
| EImm (v: val)
| ELoad (addr: reg)
| EAdd (lhs rhs: reg)
| ESub (lhs rhs: reg)
| EMul (lhs rhs: reg).

Inductive tinstr : Type :=
| ISkip
| IBreak (level: nat)
| IRet (v: reg)
| ICall (dst: reg) (name: string) (args: list reg)
| ISeq (fst snd: tinstr)
| IAssign (dst: reg) (e: texpr)
| IStore  (addr: reg) (e: reg)
| IIf (cond: reg) (trueB falseB: tinstr)
| ILoop (body: tinstr) (rest: tinstr).

Definition IWhile (cond: reg) (body: tinstr) : tinstr :=
  ILoop (ISeq (IIf cond ISkip (IBreak 0)) body) ISkip.

Definition IDoWhile (body: tinstr) (cond: reg) : tinstr :=
  ILoop (ISeq body (IIf cond ISkip (IBreak 0))) ISkip.

Record tfunction := {
    tfn_name: string;
    tfn_regs: list reg;
    tfn_code : tinstr;
    tfn_regs_no_dup : is_no_dup tfn_regs = true;
  }.
