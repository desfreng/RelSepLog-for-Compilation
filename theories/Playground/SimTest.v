From RSL Require Import Prelude.

From stdpp Require Import strings.
From Coinduction Require Import all.

From RSL Require Import Commons.Bilogic.

From RSL Require Import Simulation.Sim.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.Semantics.

Import RTLNotations.

(* Set Mangle Names. *)

Section T.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ : prog Λₜ) (Pₛ : prog Λₛ).

  Let n : reg := 1.
  Let result : reg := 2.
  Let one : reg := 3.
  Let addr : reg := 4.

  Definition fact_bad : function :=
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

  Definition fact_good : function :=
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

  Definition sim Φ '(fₜ, pcₜ) '(fₛ, pcₛ) : bilogic :=
    fun '(ρₜ, mₜ) '(ρₛ, mₛ) =>
      gfp (sim_lfp Pₜ Pₛ Φ) ([], State fₜ pcₜ ρₜ, mₜ) ([], State fₛ pcₛ ρₛ, mₛ).

  Notation "t '≲' s '{{' Φ '}}'" :=
    (sim Φ t s).

  Definition same_value '((vₜ, _) : value Λₜ) '((vₛ, _) : value Λₛ) :=
    vₜ = vₛ.

  Notation "(≈)" := same_value (at level 70).

  Lemma inv: ∀ l,
    ⊨ addr ↪ₛ l ∧ l →ₛ 1 -> (fact_good, 2) ≲ (fact_bad, 2) {{ (≈) }}.
  Proof.
    intros l [ρₜ mₜ] [ρₛ mₛ] [Haddr Hl].
    unfold_bilogic.
    revert l ρₜ mₜ ρₛ mₛ Haddr Hl.
    coinduction R cih.
    intros l ρₜ mₜ ρₛ mₛ Haddr Hl.
    (* { *)
    (*   eexists; econstructor. *)
    (* } *)

  Ltac step :=
    match goal with
    | |- can_progress _ ([], State ?f ?pc ?ρ, ?m) =>
        let H := fresh "H" in
        eassert (H: f@pc is _) by reflexivity;
        eexists
    | H: ?f @ ?pc is ?i |-
        _ ⊨ (_, State ?f ?pc _, _) ->> _ =>
        match i with
        | Inop _ => idtac f pc "nop"
        | Ireturn _ => idtac f pc "return"
        | Iop _ _ _ _ => idtac f pc "op"
        | Iload _ _ _ => idtac f pc "load"
        | Istore _ _ _ => idtac f pc "store"
        | Icond _ _ _ =>
            eapply exec_Icond;
            [apply H | reflexivity | reflexivity ];
            clear H
        end
    end.

  eapply BothSteps.
  step.
  Admitted.

  (* Lemma test: ∀ n (addr: loc) m, *)
  (*   addr ∈ dom m -> *)
  (*   ([], CallState fact_bad [n; loc_to_val addr], m) ≲ ([], CallState fact_good [n], m) *)
  (*     {{ fun '(vₜ, _) '(vₛ, _) => vₜ = vₛ }}. *)
  (* Proof. *)
  (* Admitted. *)

    (* Need to prove an invariant first. Let's do it at the start of while. *)
(* Inv:
!addr = 1.

 *)
End T.
