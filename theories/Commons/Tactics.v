From Ltac2 Require Import Ltac2 Printf.

Ltac2 check (b: bool) : unit :=
  match b with
  | true => ()
  | false => Control.zero (Tactic_failure (Some (fprintf "Check failed")))
  end.

Ltac2 print_goal () :=
  Message.print (Message.of_constr (Control.goal ())).
