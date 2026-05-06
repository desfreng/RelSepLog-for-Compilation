From stdpp Require Import prelude.
From stdpp Require Import strings.

From Coinduction Require Import all.

From RSL Require Import Commons.Language.

From RSL Require Import Refinement.Sim.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.Semantics.

Import RTLNotations.

(* Set Mangle Names. *)

Section Factorial.

  Let n : reg := 1.
  Let result : reg := 2.
  Let one : reg := 3.
  Let addr : reg := 4.

  Definition fact_bad' : function :=
    {|
      fn_name := "fact"%string;
      fn_regs := [n; addr];
      fn_entrypoint := 0;
      fn_code := <{{
            0: result := #1 -> 1;
            1: !addr := result -> 2;
            2: if n then goto 6 else goto 3;
            3: result := result * n -> 4;
            4: one := !addr -> 5;
            5: n := n - one -> 2;
            6: ret result;
        }}>;
      fn_regs_no_dup := eq_refl;
    |}.

  Definition fact_good' : function :=
    {|
      fn_name := "fact"%string;
      fn_regs := [n];
      fn_entrypoint := 0;
      fn_code := <{{
            0: result := #1 -> 1;
            1: one := #1 -> 2;
            2: if n then goto 5 else goto 3;
            3: result := result * n -> 4;
            4: n := n - one -> 2;
            5: ret result;
        }}>;
      fn_regs_no_dup := eq_refl;
    |}.

  Definition fact_good :=
    Eval cbv [fact_good' n result one addr] in fact_good'.
  Definition fact_bad :=
    Eval cbv [fact_bad' n result one addr] in fact_bad'.
End Factorial.

Section T.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ : prog Λₜ) (Pₛ : prog Λₛ).

  Notation "t '≲' s '{{' Φ '}}'" := (gfp (sim_lfp Pₜ Pₛ Φ) t s).


  Lemma test: ∀ n (addr: loc) m,
    addr ∈ dom m ->
    ([], CallState fact_bad [n; loc_to_val addr], m) ≲ ([], CallState fact_good [n], m)
      {{ fun '(vₜ, _) '(vₛ, _) => vₜ = vₛ }}.
  Proof.
  Admitted.

    (* Need to prove an invariant first. Let's do it at the start of while. *)
(* Inv:
!addr = 1.

 *)
End T.
