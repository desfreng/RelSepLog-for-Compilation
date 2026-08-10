From RSL Require Import Prelude.

From RSL Require Import Toy.Toy.
From RSL Require Import RTL.RTL.

Definition Build (T: Type) : Type :=
  node -> option (node * T * rtl_code).

Instance build_bind : MBind Build :=
  fun _ _ f m pc =>
    '(pc, x, c1) ← m pc;
    '(pc, y, c2) ← f x pc;
    mret (pc, y, c1 ∪ c2).

Instance build_ret : MRet Build :=
  fun _ x pc => Some (pc, x, ∅).

Instance build_fail : MFail Build :=
  fun _ _ _ => None.

Definition add (i: rtl_instr) : Build node :=
  fun pc =>
    let next_pc := 1 + pc in
    Some (1 + pc, pc, {[ pc := i ]}).

Definition add_next (npc: option node) (i: node -> rtl_instr) : Build node :=
  match npc with
  | Some npc => add $ i npc
  | None => mfail
  end.

Definition reserve : Build (node * (rtl_instr -> Build unit)) :=
  fun reserved_pc =>
    let fill (i: rtl_instr) : Build unit :=
      fun current_pc => Some (current_pc, (), {[ reserved_pc := i ]})
    in
    Some (1 + reserved_pc, (reserved_pc, fill), ∅).

Definition texpr_rtl (dst: reg) (e: texpr) (npc: node) : rtl_instr :=
  match e with
  | EReg r => Iop Move [r] dst npc
  | EImmInt v => Iop (ImmInt v) [] dst npc
  | EImmBool v => Iop (ImmBool v) [] dst npc
  | ELoad addr => Iload addr dst npc
  | EAdd lhs rhs => Iop Add [lhs; rhs] dst npc
  | ESub lhs rhs => Iop Sub [lhs; rhs] dst npc
  | EMul lhs rhs => Iop Mul [lhs; rhs] dst npc
  end.

Fixpoint tinstr_rtl (i: tinstr) (npc: option node) (bpc: list node) : Build node :=
  match i with
  | ISkip =>
      add_next npc $ Inop

  | IBreak level =>
      add_next (bpc !! level) $ Inop

  | IRet v =>
      add $ Ireturn v

  | ICall dst name args =>
      add_next npc $ Icall name args dst

  | IAssign dst e =>
      add_next npc $ texpr_rtl dst e

  | IStore addr e =>
      add_next npc $ Istore addr e

  | ISeq fst snd =>
      npc_snd ← tinstr_rtl snd npc bpc;
      tinstr_rtl fst (Some npc_snd) bpc

  | IIf cond trueB falseB =>
      npc_true ← tinstr_rtl trueB npc bpc;
      npc_false ← tinstr_rtl falseB npc bpc;
      add $ Icond cond npc_true npc_false

  | ILoop body rest =>
      npc_rest ← tinstr_rtl rest npc bpc;
      '(loop_init, cb) ← reserve;
      loop_fst ← tinstr_rtl body (Some loop_init) (npc_rest :: bpc);
      '() ← cb (Inop loop_fst);
      mret loop_fst
  end.

Definition compile (f: tfunction) : option rtl_function :=
  let c := tfn_code f in
  match tinstr_rtl c None [] 0 with
  | None =>
      None
  | Some (_, entry, c) =>
      Some
        {|
          rtl_fn_name := tfn_name f;
          rtl_fn_regs := tfn_regs f;
          rtl_fn_entrypoint := entry;
          rtl_fn_code := c;
          rtl_fn_regs_no_dup := tfn_regs_no_dup f;
        |}
  end.
