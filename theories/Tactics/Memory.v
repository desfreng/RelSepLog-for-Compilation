From RSL Require Import Prelude.

From stdpp Require Import fin_maps.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
From Ltac2 Require Import Notations.

Lemma get_at_union_left addr l (m1 m2: memory) :
  val_to_loc addr = Some l ->
  m1 ##ₘ m2 ->
  m2 !! l = None ->
  get_at addr (m1 ∪ m2) = get_at addr m1.
Proof.
  intros Hloc Hdij Hmem.
  unfold get_at. rewrite Hloc.
  unfold memory in *.
  now rewrite lookup_union_l.
Qed.

Lemma get_at_union_right addr l (m1 m2: memory) :
  val_to_loc addr = Some l ->
  m1 ##ₘ m2 ->
  m1 !! l = None ->
  get_at addr (m1 ∪ m2) = get_at addr m2.
Proof.
  intros Hloc Hdij Hmem.
  unfold get_at. rewrite Hloc.
  unfold memory in *.
  now rewrite lookup_union_r.
Qed.

Lemma get_at_singl addr l v :
  val_to_loc addr = Some l ->
  get_at addr {[ l := v ]} = Some v.
Proof.
  intros Hloc.
  unfold get_at. rewrite Hloc.
  unfold memory in *.
  now rewrite lookup_singleton_eq.
Qed.

(** A small utility to print the goal *)
Ltac2 print_goal () :=
  let g := Control.goal () in
  Message.print (Message.of_constr g).

Ltac2 rec first_of tacs : unit :=
  match tacs with
  | [] => Control.backtrack_tactic_failure "Empty first list"
  | tac :: tacs =>
      Control.enter (fun _ => orelse tac (fun _ => first_of tacs))
  end.

Ltac2 assert_by h cst tac :=
  Std.assert
    (Std.AssertType
       (Some (Std.IntroNaming (Std.IntroIdentifier h)))
       cst
       (Some tac)).

(* Ltac2 debug (tac: unit -> unit) () : unit := *)
(*   match Control.case tac with *)
(*   | Val (x, k) => Control.plus (fun () => x) k *)
(*   | Err e => *)
(*       let einfo := Control.current_exninfo () *)
(*       in Control.throw_bt (Debug (Control.print_exn e)) einfo *)
(*   end. *)

Ltac2 in_hyp h : Std.clause :=
  {
    Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)];
    Std.on_concl := Std.NoOccurrences
  }.

Ltac2 in_goal : Std.clause :=
  {
    Std.on_hyps := Some [];
    Std.on_concl := Std.AllOccurrences
  }.

Ltac2 rewrite_in_hyp thm hyps cl tac :=
  Std.rewrite false
    [{
      Std.rew_orient := None;
      Std.rew_repeat := Std.Precisely 1;
      Std.rew_equatn :=
              (fun () => (thm, Std.ExplicitBindings hyps))
    }]
    cl
    tac.

Ltac2 call_solve_disjoint () : unit :=
  Control.enter (fun () => ltac1:(solve_map_disjoint)).

Ltac2 simgetpair hloc m1 m2 place : unit :=
  let hdij := Fresh.in_goal @Hdij in
  assert_by hdij '($m1 ##ₘ $m2) call_solve_disjoint;
  first_of [
      (fun () => rewrite_in_hyp 'get_at_union_left
                 [(Std.AnonHyp 1, Control.hyp hloc);
                  (Std.AnonHyp 2, Control.hyp hdij)]
                 place (Some call_solve_disjoint));
      (fun () => rewrite_in_hyp 'get_at_union_right
                 [(Std.AnonHyp 1, Control.hyp hloc);
                  (Std.AnonHyp 2, Control.hyp hdij)]
                 place (Some call_solve_disjoint))
    ];
  Std.clear [hdij].

Ltac2 discr_or_inj h :=
  first_of [
      (fun () =>
         Std.injection
           false
           (Some [Std.IntroNaming (Std.IntroIdentifier h)])
           (Some (Std.ElimOnIdent h))
      );
      (fun () =>
         Std.discriminate false (Some (Std.ElimOnIdent h))
      );
      (fun _ => ())
    ].

Ltac2 rec simget0 () : unit :=
  lazy_match! goal with
  | [hloc: val_to_loc ?_addr = Some _,
       hget: get_at ?_addr ?m = _ |- _] =>
      lazy_match! m with
      | ?m1 ∪ ?m2 =>
          simgetpair hloc m1 m2 (in_hyp hget);
          try0 simget0
      | {[_ := _ ]} =>
          rewrite_in_hyp 'get_at_singl
            [(Std.AnonHyp 1, Control.hyp hloc)] (in_hyp hget) None;
          discr_or_inj hget
      end
  | [hloc: val_to_loc ?_addr = Some _ |- get_at ?_addr ?m = _ ] =>
      lazy_match! m with
      | ?m1 ∪ ?m2 =>
          simgetpair hloc m1 m2 in_goal;
          try0 simget0
      | {[_ := _ ]} =>
          rewrite_in_hyp 'get_at_singl
            [(Std.AnonHyp 1, Control.hyp hloc)] in_goal None;
          try0 Std.reflexivity
      end
  end.

Ltac simget :=
  match goal with
  | [hloc: val_to_loc ?_addr = Some _,
       hget: get_at ?_addr ?m = _ |- _] =>
      rewrite
        !(get_at_union_right _ _ _ _ hloc),
        !(get_at_union_left _ _ _ _ hloc),
        !(get_at_singl _ _ _ hloc)
          in hget by solve_map_disjoint;
      inv hget
  | [hloc: val_to_loc ?_addr = Some _
     |- get_at ?_addr ?m = _ ] =>
      rewrite
        !(get_at_union_right _ _ _ _ hloc),
        !(get_at_union_left _ _ _ _ hloc),
        !(get_at_singl _ _ _ hloc)
            by solve_map_disjoint;
      try easy
  end.

Lemma set_at_some addr l v old m:
  val_to_loc addr = Some l ->
  get_at addr m = Some old ->
  set_at addr v m = Some (alter (fun _ => v) l m).
Proof.
  unfold set_at, get_at.
  intros Hloc Hget.
  rewrite Hloc in *.
  destruct (m !! l) as [[]|]; congruence.
Qed.

Lemma set_at_none addr v m:
  get_at addr m = None ->
  set_at addr v m = None.
Proof.
  unfold set_at, get_at.
  intros Hget.
  destruct (val_to_loc addr) as [l|].
  - destruct (m !! l) as [[]|]; congruence.
  - reflexivity.
Qed.

Lemma alter_union_right f l (m1 m2: memory) :
  m1 ##ₘ m2 ->
  m1 !! l = None ->
  alter f l (m1 ∪ m2) = m1 ∪ alter f l m2.
Proof using Type.
  intros Hdij Hnin.
  unfold union, map_union.
  rewrite (alter_union_with_r _ _ m1).
  - reflexivity.
  - intros x y H1 H2. exfalso.
    rewrite map_disjoint_alt in Hdij.
    destruct (Hdij l) as [? | ?]; congruence.
  - intros x H1 H2.
    unfold memory in *.
    congruence.
Qed.

Lemma alter_union_left f l (m1 m2: memory) :
  m1 ##ₘ m2 ->
  m2 !! l = None ->
  alter f l (m1 ∪ m2) = alter f l m1 ∪ m2.
Proof using Type.
  intros Hdij Hnin.
  unfold union, map_union.
  rewrite (alter_union_with_l _ _ m1).
  - reflexivity.
  - intros x y H1 H2. exfalso.
    rewrite map_disjoint_alt in Hdij.
    destruct (Hdij l) as [? | ?]; congruence.
  - intros x H1 H2.
    unfold memory in *.
    congruence.
Qed.


Lemma alter_singleton f l old :
  alter f l ({[ l := old ]} : memory) = ({[l := f old ]} : memory).
Proof using Type.
  unfold memory in *.
  now rewrite (alter_singleton_eq).
Qed.
