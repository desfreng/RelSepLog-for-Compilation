From RSL Require Import Prelude.

From RSL.Logic Require Import rPropDef BI.

Ltac smap :=
  rewrite ?map_union_assoc;
  repeat
    (lazymatch goal with
     | [ |- context [∅ ∪ _]] => rewrite map_empty_union
     | [ |- context [_ ∪ ∅]] => rewrite map_union_empty
     | [ H: context [∅ ∪ _] |- _ ] => rewrite map_empty_union in H
     | [ H: context [_ ∪ ∅] |- _ ] => rewrite map_union_empty in H
     end);
  try done.

From Ltac2 Require Import Ltac2 RedFlags.

Local Ltac2 to_unfold () : Std.reference list :=
  [
    reference:(bi_emp_valid);
    reference:(bi_intuitionistically);
    reference:(bi_absorbingly);
    reference:(bi_affinely);
    reference:(bi_wand_iff);
    reference:(bi_iff);
    reference:(bi_entails);
    reference:(bi_pure);
    reference:(bi_and);
    reference:(bi_or);
    reference:(bi_impl);
    reference:(bi_forall);
    reference:(bi_exist);
    reference:(bi_sep);
    reference:(bi_wand);
    reference:(bi_persistently);
    reference:(bi_later);
    reference:(bi_emp)
  ].

Ltac2 reduce_list cl :=
  let l := List.map (fun r => (r, Std.AllOccurrences)) (to_unfold ()) in
  Std.unfold l cl.

Ltac2 unseal_ cl :=
  reduce_list cl;
  Std.simpl beta None cl;
  Tactic.unseal cl.

Ltac2 Notation "unseal" cl(opt(seq("in", clause))) :=
  unseal_ (default_on_concl cl).

Tactic Notation "unseal" := ltac2:(unseal).
Tactic Notation "unseal" "in" ident(H) :=
  let tac :=
    ltac2:(h |-
             let h := Option.get (Ltac1.to_ident h) in
             let cl :=
               {
                 Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)];
                 Std.on_concl := Std.NoOccurrences
               }
             in unseal_ cl)
  in tac H.
