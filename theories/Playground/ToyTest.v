From RSL Require Import Prelude.

From stdpp Require Import prelude strings fin_maps sorting.

From RSL.Toy Require Import Toy Notations Compile.
From RSL.RTL Require Import RTL Notations.

Import ToyNotations.
Import RTLNotations.

Section Playground.
  Let n : reg := 1.
  Let result : reg := 2.
  Let one : reg := 3.

  Definition factorial_program : tfunction :=
    {|
      tfn_name := "fact"%string;
      tfn_regs := [n];
      tfn_code :=
        <{|
            result := #1;
            one := #1;
            while n {
                result := result * n;
                n := n - one
            };
            return result
          |}>;
      tfn_regs_no_dup := eq_refl;
    |}.

  Definition sortp (a b: node * rtl_instr) : Prop :=
    match b, a with
    | (x, _), (y, _) => x <= y
    end.

  (* Definition compile_and_opt (p: tfunction) : option function := *)
  (*   match compile p with *)
  (*   | Some c => Some $ remove_dead_code $ remove_nops c *)
  (*   | None => None *)
  (*   end. *)

  (* Definition pp (p: option function) : list (node * instr) := *)
  (*   match p with *)
  (*   | Some m => merge_sort sortp $ map_to_list $ fn_code m *)
  (*   | None => [] *)
  (*   end. *)

  (* Compute pp $ compile factorial_program. *)

  (* Compute pp $ compile_and_opt factorial_program. *)
End Playground.
