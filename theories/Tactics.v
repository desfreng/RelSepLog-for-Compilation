Ltac inv H := inversion H; subst; clear H.

Ltac pc_inj :=
  match goal with
  | [ H1: ?f = Some (?x1 ?x2), H2: ?f = Some (?y1 ?y2) |- _ ] =>
      let H := fresh in
      assert (H: y1 y2 = x1 x2) by congruence; inv H; clear H2
  | [ H1: ?f = Some ?x, H2: ?f = Some ?y |- _ ] =>
      let H := fresh in
      assert (H: y = x) by congruence; subst; clear H2
  end.
