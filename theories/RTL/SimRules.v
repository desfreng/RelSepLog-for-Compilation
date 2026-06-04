From RSL Require Import Prelude RelLogic.

From Coinduction Require Import all.

From RSL Require Import Simulations.FreeSim.
From RSL Require Import Simulations.FreeSimRules.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Notations.

Import RTLNotations.

Section Rules.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation fsim := (fsim WfNat WfNat Pₜ Pₛ).
  Abbreviation fsim_lfp := (fsim_lfp WfNat WfNat Pₜ Pₛ).
  Abbreviation rlogic := (rlogic _ _).

  Definition sim GFP Q (stepₜ: nat) fₜ pcₜ (stepₛ: nat) fₛ pcₛ : rlogic :=
    let sim_rtl Φ : rlogic :=
      (fun ρₜ ρₛ mₜ mₛ =>
         fsim_lfp GFP Φ
           stepₜ ([], State fₜ pcₜ ρₜ, mₜ)
           stepₛ ([], State fₛ pcₛ ρₛ, mₛ))
    in
    ⦇ ∀ Φ,
        ⌜∀ vₜ vₛ mₜ mₛ, Q vₜ vₛ mₜ mₛ -> Φ (vₜ, mₜ) (vₛ, mₛ)⌝ ->
        sim_rtl Φ ⦈.

  Notation
    "C ⊢ '⟨' ft '@' pct ',' j '⟩' '≲' '⟨' fs '@' pcs ',' i '⟩' '{{' Φ '}}'" :=
    (sim (elem C) Φ j ft pct i fs pcs)
      (at level 1, ft at level 0, fs at level 0, no associativity).

  Lemma both_ret (C : Chain fsim_lfp) Q j fₜ pcₜ i fₛ pcₛ :
    ∀ rₜ vₜ rₛ vₛ,
    fₜ@pcₜ is <{ ret rₜ }> ->
    fₛ@pcₛ is <{ ret rₛ }> ->
    ⊨ rₜ ⇒ₜ vₜ ->
      rₛ ⇒ₛ vₛ ->
      ⌜Q vₜ vₛ⌝ₘ ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }}.
  Proof using Type.
    intros rt vt rs vs Hpct Hpcs.
    intros ρₜ ρₛ mₜ mₛ Ht Hs HQ Ψ Hpost. simp.
    eapply FSourceSteps with (i' := 0).
    { econstructor; eassumption || reflexivity. }
    eapply FTargetSteps.
    { eexists; econstructor; eassumption || reflexivity. }
    intros t' Hstep. inv Hstep.
    exists 0.
    eapply FBothFinal.
    do 2 econstructor. repeat split.
    now apply Hpost.
  Qed.

  Lemma source_nop (C : Chain fsim_lfp) Q j fₜ pcₜ i fₛ pcₛ :
    ∀ pc,
    fₛ@pcₛ is <{ nop -> pc }> ->
    ⊨ C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pc, S i⟩ {{ Q }} ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }}.
  Proof using Type.
    intros pc Hpc.
    intros ρₜ ρₛ mₜ mₛ H Ψ Hpost. simp.
    eapply FSourceSteps.
    - constructor; eassumption.
    - now apply H.
  Qed.

  Lemma target_nop (C : Chain fsim_lfp) Q j fₜ pcₜ i fₛ pcₛ :
    ∀ pc,
    fₜ@pcₜ is <{ nop -> pc }> ->
    ⊨ C ⊢ ⟨fₜ @ pc, S j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }} ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }}.
  Proof using Type.
    intros pc Hpc.
    intros ρₜ ρₛ mₜ mₛ H Ψ Hpost. simp.
    eapply FTargetSteps.
    - eexists. constructor; eassumption.
    - intros t Hstep. inv Hstep.
      eexists. now apply H.
  Qed.

  Lemma mapMtoMap {A B : Type} : ∀ (f : A -> B) args,
    mapM (fun x => Some (f x)) args = Some (map f args).
  Proof using Type.
    intros f args.
    induction args as [ | hd tl IH ].
    - reflexivity.
    - simpl. now rewrite IH.
  Qed.

  Lemma source_op (C : Chain fsim_lfp) Q j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst op regs args v,
    fₛ@pcₛ is <{ dst := @op regs -> pc }> ->
    eval_op op args = Some v ->
    ⊨ regs ⇒ₛ args ->
      ⟦ dst ⇐ₛ v ⟧ C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pc, S i⟩ {{ Q }} ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }}.
  Proof using Type.
    intros pc dst op regs args v Hpc Hv.
    intros ρₜ ρₛ mₜ mₛ Harg [? [Hnew Hsim]] Ψ Hpost. simp.

    rewrite mapMtoMap in Harg.
    injection Harg as Harg.

    injection Hnew as Hnew.

    eapply FSourceSteps.
    - econstructor; eassumption || reflexivity.
    - now apply Hsim.
  Qed.

  Lemma target_op (C : Chain fsim_lfp) Q j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst op regs args v,
    fₜ@pcₜ is <{ dst := @op regs -> pc }> ->
    eval_op op args = Some v ->
    ⊨ regs ⇒ₜ args ->
      ⟦ dst ⇐ₜ v ⟧ C ⊢ ⟨fₜ @ pc, S j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }} ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }}.
  Proof using Type.
    intros pc dst op regs args v Hpc Hv.
    intros ρₜ ρₛ mₜ mₛ Harg [? [Hnew Hsim]] Ψ Hpost. simp.

    rewrite mapMtoMap in Harg.
    injection Harg as Harg.

    injection Hnew as Hnew.

    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep.
      eexists. now apply Hsim.
  Qed.

  Lemma source_load (C : Chain fsim_lfp) Q j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst src addr v,
    fₛ@pcₛ is <{ dst := !src -> pc }> ->
    ⊨ src ⇒ₛ addr ->
      addr →ₛ v ->
      ⟦ dst ⇐ₛ v ⟧ C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pc, S i⟩ {{ Q }} ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }}.
  Proof using Type.
    intros pc dst src addr v Hpc.
    intros ρₜ ρₛ mₜ mₛ Hsrc Haddr [? [Hnew Hsim]] Ψ Hpost. simp.

    injection Hsrc as Hsrc.
    injection Hnew as Hnew.

    eapply FSourceSteps.
    - econstructor; eassumption || reflexivity.
    - now eapply Hsim.
  Qed.

  Lemma target_load (C : Chain fsim_lfp) Q j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst src addr v,
    fₜ@pcₜ is <{ dst := !src -> pc }> ->
    ⊨ src ⇒ₜ addr ->
      addr →ₜ v ->
      ⟦ dst ⇐ₜ v ⟧ C ⊢ ⟨fₜ @ pc, S j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }} ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }}.
  Proof using Type.
    intros pc dst src addr v Hpc.
    intros ρₜ ρₛ mₜ mₛ Hsrc Haddr [? [Hnew Hsim]] Ψ Hpost. simp.

    injection Hsrc as Hsrc.
    injection Hnew as Hnew.

    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep.
      eexists. now apply Hsim.
  Qed.

  Lemma source_store (C : Chain fsim_lfp) Q j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst src addr v,
    fₛ@pcₛ is <{ !dst := src -> pc }> ->
    ⊨ src ⇒ₛ v ->
      dst ⇒ₛ addr ->
      ⟦ addr ←ₛ v ⟧ C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pc, S i⟩ {{ Q }} ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }}.
  Proof using Type.
    intros pc dst src addr v Hpc.
    intros ρₜ ρₛ mₜ mₛ Hsrc Haddr [? [Hnew Hsim]] Ψ Hpost. simp.

    injection Hsrc as Hsrc.
    injection Haddr as Haddr.

    eapply FSourceSteps.
    - econstructor; eassumption || reflexivity.
    - now eapply Hsim.
  Qed.

  Lemma target_store (C : Chain fsim_lfp) Q j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst src addr v,
    fₜ@pcₜ is <{ !dst := src -> pc }> ->
    ⊨ src ⇒ₜ v ->
      dst ⇒ₜ addr ->
      ⟦ addr ←ₜ v ⟧ C ⊢ ⟨fₜ @ pc, S j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }} ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }}.
  Proof using Type.
    intros pc dst src addr v Hpc.
    intros ρₜ ρₛ mₜ mₛ Hsrc Haddr [? [Hnew Hsim]] Ψ Hpost. simp.

    injection Hsrc as Hsrc.
    injection Haddr as Haddr.

    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep.
      eexists. now apply Hsim.
  Qed.

  Lemma source_if (C : Chain fsim_lfp) Q j fₜ pcₜ i fₛ pcₛ :
    ∀ pc_true pc_false reg v,
    fₛ@pcₛ is <{ if reg then goto pc_true else goto pc_false }> ->
    ⊨ reg ⇒ₛ v ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ if (v =? 0)%Z then pc_true else pc_false, i⟩ {{ Q }} ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }}.
  Proof using Type.
    intros pc_true pc_false reg Hpc Hv.
    intros ρₜ ρₛ mₜ mₛ Harg Hsim Ψ Hpost. simp.

    injection Harg as Harg.

    eapply FSourceSteps.
    - econstructor; eassumption || reflexivity.
    - now apply Hsim.
  Qed.

  Lemma target_if (C : Chain fsim_lfp) Q j fₜ pcₜ i fₛ pcₛ :
    ∀ pc_true pc_false reg v,
    fₜ@pcₜ is <{ if reg then goto pc_true else goto pc_false }> ->
    ⊨ reg ⇒ₜ v ->
      C ⊢ ⟨fₜ @ if (v =? 0)%Z then pc_true else pc_false, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }} ->
      C ⊢ ⟨fₜ @ pcₜ, j⟩ ≲ ⟨fₛ @ pcₛ, i⟩ {{ Q }}.
  Proof using Type.
    intros pc_true pc_false reg Hpc Hv.
    intros ρₜ ρₛ mₜ mₛ Harg Hsim Ψ Hpost. simp.

    injection Harg as Harg.

    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep.
      eexists. now apply Hsim.
  Qed.

End Rules.
