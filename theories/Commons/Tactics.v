From RSL Require Import Prelude.

From Ltac2 Require Import Ltac2 Printf.

Ltac2 goal () : Std.clause := default_on_concl None.

Ltac2 check (b: bool) : unit :=
  match b with
  | true => ()
  | false => Control.zero (Tactic_failure (Some (fprintf "Check failed")))
  end.

Ltac2 print_goal () :=
  Message.print (Message.of_constr (Control.goal ())).

Ltac2 unfold_list l cl :=
  let l := List.map (fun c => (c, Std.AllOccurrences)) l
  in Std.unfold l cl.

Ltac2 rewrite_list rl cl :=
  let f c :=
    {
      Std.rew_orient := Some Std.LTR;
      Std.rew_repeat := Std.RepeatStar;
      Std.rew_equatn := (fun _ => (c, Std.NoBindings))
    }
  in
  let l := List.map f rl in
  Std.rewrite false l cl None.
