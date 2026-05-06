From RSL Require Import Prelude.

From stdpp Require Import gmap.
From stdpp Require Import sets.

From RSL Require Import RTL.RTL.

Fixpoint last_succ (fuel: nat) (c: code) (n: node) : node :=
  match fuel with
  | 0 => n
  | S f =>
      match c !! n with
      | Some (Inop next) =>
          if (next =? n)
          then n
          else last_succ f c next
      | _ => n
      end
  end.

Definition redirect_instr (f: node -> node) (i: instr) : instr :=
  match i with
  | Inop succ => Inop (f succ)
  | Iop op args dst succ => Iop op args dst (f succ)
  | Iload addr dst succ => Iload addr dst (f succ)
  | Istore addr src succ => Istore addr src (f succ)
  | Icall sig args dst succ => Icall sig args dst (f succ)
  | Icond cond ifso ifnot => Icond cond (f ifso) (f ifnot)
  | Ireturn reg => Ireturn reg
  end.

Definition remove_nops (fn: function) : function :=
  let c := fn_code fn in
  let max_fuel := size c in
  let f := last_succ max_fuel c in
  let new_c := fmap (redirect_instr f) c in
  let new_entry := f $ fn_entrypoint fn in
  {|
    fn_name := fn_name fn;
    fn_regs := fn_regs fn;
    fn_entrypoint := new_entry;
    fn_code := new_c;
    fn_regs_no_dup := fn_regs_no_dup fn;
  |}.

(* Fixpoint find_reachable (fuel: nat) (c: code) (worklist: list node) *)
(*   (visited: gset node) : gset node := *)
(*   match fuel with *)
(*   | 0 => visited *)
(*   | S f => *)
(*       match worklist with *)
(*       | [] => visited *)
(*       | n :: rest => *)
(*           if bool_decide (n ∈ visited) then *)
(*             find_reachable f c rest visited *)
(*           else *)
(*             let visited' := {[ n ]} ∪ visited in *)
(*             match c !! n with *)
(*             | Some i => *)
(*                 find_reachable f c (successors i ++ rest) visited' *)
(*             | None => *)
(*                 find_reachable f c rest visited' *)
(*             end *)
(*       end *)
(*   end. *)

(* Definition remove_dead_code (fn: function) : function := *)
(*   let c := fn_code fn in *)
(*   let max_fuel := 3 * size c + 1 in *)
(*   let reachable_set := find_reachable max_fuel c [fn_entrypoint fn] ∅ in *)
(*   let new_c := filter (fun '(k, _) => bool_decide (k ∈ reachable_set)) c in *)
(*   {| *)
(*     fn_name := fn_name fn; *)
(*     fn_regs := fn_regs fn; *)
(*     fn_entrypoint := fn_entrypoint fn; *)
(*     fn_code := new_c; *)
(*     fn_regs_no_dup := fn_regs_no_dup fn; *)
(*   |}. *)
