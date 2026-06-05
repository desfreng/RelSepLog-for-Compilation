From RSL Require Import Prelude RelLogic.

From stdpp Require Import strings.
From stdpp Require Import gmap.
From stdpp Require Import tactics.

From Coinduction Require Import all.

From RSL Require Import Simulations.FreeSim.
From RSL Require Import Simulations.FreeSimRules.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.SimRules.

Import RTLNotations.

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
      fn_code := <<{{
            0: result := #1 -> 1;
            1: !addr := result -> 2;
            2: if n then goto 6 else goto 3;
            3: result := result * n -> 4;
            4: one := !addr -> 5;
            5: n := n - one -> 2;
            6: ret result;
        }}>>;
      fn_regs_no_dup := eq_refl;
    |}.

  Definition fact_good : function :=
    {|
      fn_name := "fact"%string;
      fn_regs := [n];
      fn_entrypoint := 0;
      fn_code := <<{{
            0: result := #1 -> 1;
            1: one := #1 -> 2;
            2: if n then goto 5 else goto 3;
            3: result := result * n -> 4;
            4: n := n - one -> 2;
            5: ret result;
        }}>>;
      fn_regs_no_dup := eq_refl;
    |}.

  Abbreviation fsim := (fsim WfNat WfNat Pₜ Pₛ).
  Abbreviation fsim_lfp := (fsim_lfp WfNat WfNat Pₜ Pₛ).

  Notation "C ⊢ '⟨' ft '@' pct ',' j '⟩' '≲' '⟨' fs '@' pcs ',' i '⟩' '{{' Φ '}}'" :=
    (sim Pₜ Pₛ (elem C) Φ j ft pct i fs pcs)
      (at level 1, ft at level 0, fs at level 0, no associativity).

  (* Definition veq (vₜ vₛ : val) (mₜ mₛ: memory) := *)
  (*   vₜ = vₛ. *)

  (* Haddr : get_reg addr ρₛ = v *)
  (* ρₜ : regmap *)
  (* Ht : get_reg n ρₜ = x *)
  (* Hs : get_reg n ρₛ = x *)
  (* l : loc *)
  (* Hloc : val_to_loc v = Some l *)
  (* mₛ : memory *)
  (* Hmem : mₛ !! l = Some 1%Z *)
  (* Hreg : get_reg result ρₛ = 1%Z *)
  (* Hreg0 : get_reg result ρₜ = 1%Z *)
  (* Hreg1 : get_reg one ρₜ = 1%Z *)
  (* ============================ *)
  (* C ⊢ ⟨ fact_good @ 2, 2 ⟩ ≲ ⟨ fact_bad @ 2, 2 ⟩ {{veq}} (ρₜ, mₜ) (ρₛ, mₛ) *)

  (* Lemma inv (C: Chain fsim_lfp) : ∀  loc, *)
  (*   ⊨ addr ⇒ₛ loc -> *)
  (*   result ₜ≈ₛ result -> *)
  (*   n ₜ≈ₛ n -> *)
  (*   one ⇒ₜ 1 -> *)
  (*   loc →ₛ 1 -> *)
  (*   C ⊢ ⟨fact_good @ 2, 0⟩ ≲ ⟨fact_bad @ 2, 0⟩ {{ veq }}. *)
  (* Proof using Type. *)
  (*   intros loc. *)
  (*   intros ρₜ ρₛ mₜ mₛ Haddr Hres Hn Hone Hloc Ψ Hpost. simp. *)
  (*   injection Haddr as Haddr. *)
  (*   injection Hres as Hres. *)
  (*   injection Hn as Hn. *)
  (*   injection Hone as Hone. *)

  (*   eapply @coind_rule. *)
  (*   intros C' j i CIH. *)
  (*   cut (C' ⊢ ⟨ fact_good @ 2, 0 ⟩ ≲ ⟨ fact_bad @ 2, 0 ⟩ {{veq}} ρₜ ρₛ mₜ mₛ). *)
  (*   { *)
  (*     intros H. unfold sim in H. simp. *)
  (*     eapply (@fsim_lfp_mono). *)
  (*     - eapply (H Ψ). *)
  (*       apply Hpost. *)
  (*     - destruct j. *)
  (*       + now right. *)
  (*       + left. simpl. lia. *)
  (*     - destruct i. *)
  (*       + now right. *)
  (*       + left. simpl. lia. *)
  (*   } *)
  (*   eapply source_if; try reflexivity. *)
  (* (*   iRegUpdate. *) *)

  (*   admit. *)
  (* Admitted. *)

  (*   unfold_bilogic. *)
  (*   simpl_memory by idtac. *)

  (*   eapply source_op; try reflexivity. *)
  (*   { reflexivity. } *)
  (*   iRegUpdate. *)

  (*   eapply target_op; try reflexivity. *)
  (*   { reflexivity. } *)
  (*   iRegUpdate. *)

  (*   eapply source_store; try reflexivity. *)
  (*   rewrite Haddr, Hreg. *)
  (*   iMemUpdate. *)

  (*   eapply target_op; try reflexivity. *)
  (*   { reflexivity. } *)
  (*   iRegUpdate. *)

  (* Admitted. *)
End T.
