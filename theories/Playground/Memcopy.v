From RSL Require Import RelLogic Prelude.

From stdpp Require Import strings.
From stdpp Require Import gmap.
From stdpp Require Import tactics.

From RSL Require Import Simulations.FreeSim.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.Semantics.

From RSL Require Import RTL.SimRules.
From RSL Require Import RTL.TargetRules.
From RSL Require Import RTL.SourceRules.

Import RTLNotations.

Section T.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ : prog Λₜ) (Pₛ : prog Λₛ).

  Abbreviation fsim := (fsim WfNat WfNat Pₜ Pₛ).

  Let reg_src : reg := 1.
  Let reg_dst : reg := 2.
  Let reg_len : reg := 3.
  Let reg_val : reg := 4.
  Let reg_four : reg := 5.
  Let reg_len_round : reg := 6.

  Definition memcpy_simple : function :=
    {|
      fn_name := "memcpy"%string;
      fn_regs := [reg_src; reg_dst; reg_len];
      fn_entrypoint := 0;
      fn_code :=
        <<{{
              (* Loop *)
              0: if reg_len then goto 6 else goto 1;

              (* Body *)
              1: reg_val := !reg_src -> 2;
              2: !reg_dst := reg_val -> 3;
              3: reg_src := reg_src++ -> 4;
              4: reg_dst := reg_dst++ -> 5;
              5: reg_len := reg_len-- -> 0;

              (* End *)
              6: ret reg_dst;
          }}>>;
      fn_regs_no_dup := eq_refl;
    |}.

  Definition memcpy_unroll4 : function :=
    {|
      fn_name := "memcpy_unroll4"%string;
      fn_regs := [reg_src; reg_dst; reg_len];
      fn_entrypoint := 0;
      fn_code :=
        <<{{
              0: reg_four := #4 -> 1;

              (* Rounding *)
              1: reg_len_round := reg_len / reg_four -> 2;
              2: reg_len_round := reg_len_round * reg_four -> 3;

              (* Main Loop Head *)
              3: if reg_len then goto 22 else goto 4;

              (* Copy 1 *)
              4: reg_val := !reg_src -> 5;
              5: !reg_dst := reg_val -> 6;
              6: reg_src := reg_src++ -> 7;
              7: reg_dst := reg_dst++ -> 8;

              (* Copy 2 *)
              8: reg_val := !reg_src -> 9;
              9: !reg_dst := reg_val -> 10;
              10: reg_src := reg_src++ -> 11;
              11: reg_dst := reg_dst++ -> 12;

              (* Copy 3 *)
              12: reg_val := !reg_src -> 13;
              13: !reg_dst := reg_val -> 14;
              14: reg_src := reg_src++ -> 15;
              15: reg_dst := reg_dst++ -> 16;

              (* Copy 4 *)
              16: reg_val := !reg_src -> 17;
              17: !reg_dst := reg_val -> 18;
              18: reg_src := reg_src++ -> 19;
              19: reg_dst := reg_dst++ -> 20;

              (* Decrement counters and repeat Main Loop *)
              20: reg_len_round := reg_len_round - reg_four -> 21;
              21: reg_len := reg_len - reg_four -> 3;

              (* Tail Loop Head *)
              22: if reg_len then goto 28 else goto 23;

              (* Tail Loop Body (1-by-1 copy) *)
              23: reg_val := !reg_src -> 24;
              24: !reg_dst := reg_val -> 25;
              25: reg_src := reg_src++ -> 26;
              26: reg_dst := reg_dst++ -> 27;
              27: reg_len := reg_len-- -> 22;

              (* End *)
              28: ret reg_dst;
          }}>>;
      fn_regs_no_dup := eq_refl;
    |}.
End T.
