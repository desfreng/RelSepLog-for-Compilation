From RSL Require Import Prelude.

From stdpp Require Import strings.
From Coinduction Require Import all.

From RSL Require Import Commons.Bilogic.

From RSL Require Import Simulations.FreeSim.

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

  Definition sim Φ (stepₜ: nat) '(fₜ, pcₜ) (stepₛ: nat) '(fₛ, pcₛ) : bilogic :=
    let Φ := fun '(vₜ, mₜ) '(vₛ, mₛ) => Φ vₜ vₛ mₜ mₛ in
    fun '(ρₜ, mₜ) '(ρₛ, mₛ) =>
      gfp (fsim_lfp _ _ Pₜ Pₛ Φ) stepₜ ([], State fₜ pcₜ ρₜ, mₜ) stepₛ ([], State fₛ pcₛ ρₛ, mₛ).

  Hint Unfold sim : custom_bilogic.

  Notation "t '⟨' iₜ '≲' iₛ '⟩' s '{{' Φ '}}'" :=
    (sim Φ iₜ t iₛ s)
      (at level 1, no associativity).

  Definition same_value (vₜ vₛ: val) (_ _: memory) :=
    vₜ = vₛ.

  Notation "(≈)" := same_value (at level 0).

  Lemma inv: ∀ fuel l,
    ⊨ one ↪ₜ 1 ->
    addr ↪ₛ l ->
    l →ₛ 1 ->
    (fact_good, 2) ⟨fuel ≲ fuel⟩ (fact_bad, 2) {{ (≈) }}.
  Proof using Type.
  Admitted.
End T.
