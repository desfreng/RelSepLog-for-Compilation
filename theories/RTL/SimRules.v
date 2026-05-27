From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Commons.Bilogic.
From RSL Require Import Commons.Logic.

From RSL Require Import Simulations.FreeSim.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Notations.

Import RTLNotations.

Section Rules.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: val -> val -> memory -> memory -> Prop).

  Definition sim Φ (stepₜ: nat) '(fₜ, pcₜ) (stepₛ: nat) '(fₛ, pcₛ) : bilogic :=
    let Φ := fun '(vₜ, mₜ) '(vₛ, mₛ) => Φ vₜ vₛ mₜ mₛ in
    fun '(ρₜ, mₜ) '(ρₛ, mₛ) =>
      gfp (fsim_lfp _ _ Pₜ Pₛ Φ) stepₜ ([], State fₜ pcₜ ρₜ, mₜ) stepₛ ([], State fₛ pcₛ ρₛ, mₛ).

  Hint Unfold sim : custom_bilogic.

  Notation "t '⟨' iₜ '≲' iₛ '⟩' s '{{' Φ '}}'" :=
    (sim Φ iₜ t iₛ s)
      (at level 1, no associativity).

  Lemma source_nop iₜ iₛ fₜ fₛ pcₜ pcₛ : ∀ pc,
    fₛ@pcₛ is <{ nop -> pc }> ->
    ⊨ (fₜ, pcₜ) ⟨iₜ ≲ S iₛ⟩ (fₛ, pc) {{ Φ }} ->
    (fₜ, pcₜ) ⟨iₜ ≲ iₛ⟩ (fₛ, pcₛ) {{ Φ }}.
  Proof using Type.
    intros pc Hpc [ρₜ mₜ] [ρₛ mₛ] H.
    unfold_bilogic.
    apply (@fsim_roll Λₜ Λₛ).
    eapply FSourceSteps.
    - constructor; eassumption.
    - eapply (@fsim_unroll Λₜ Λₛ).
      apply H.
  Qed.

  Lemma target_nop iₜ iₛ fₜ fₛ pcₜ pcₛ : ∀ pc,
    fₜ@pcₜ is <{ nop -> pc }> ->
    ⊨ (fₜ, pc) ⟨S iₜ ≲ iₛ⟩ (fₛ, pcₛ) {{ Φ }} ->
    (fₜ, pcₜ) ⟨iₜ ≲ iₛ⟩ (fₛ, pcₛ) {{ Φ }}.
  Proof using Type.
    intros pc Hpc [ρₜ mₜ] [ρₛ mₛ] H.
    unfold_bilogic.
    apply (@fsim_roll Λₜ Λₛ).
    eapply FTargetSteps.
    - eexists. constructor; eassumption.
    - intros t Hstep. inv Hstep.
      eexists.
      eapply (@fsim_unroll Λₜ Λₛ).
      apply H.
  Qed.

  Lemma source_op iₜ iₛ fₜ fₛ pcₜ pcₛ :
    ∀ pc dst op regs args v,
    fₛ@pcₛ is <{ dst := @op regs -> pc }> ->
    eval_op op args = Some v ->
    ⊨ regs ↪ₛ args ->
      ⟦ dst ↩ₛ v ⟧ (fₜ, pcₜ) ⟨iₜ ≲ S iₛ⟩ (fₛ, pc) {{ Φ }} ->
      (fₜ, pcₜ) ⟨iₜ ≲ iₛ⟩ (fₛ, pcₛ) {{ Φ }}.
  Proof using Type.
    intros pc dst op regs args v Hpc Hv [ρₜ mₜ] [ρₛ mₛ].
    intros Harg Hsim. unfold_bilogic.
    apply (@fsim_roll Λₜ Λₛ). subst.
    eapply FSourceSteps.
    - econstructor; eassumption || reflexivity.
    - eapply (@fsim_unroll Λₜ Λₛ).
      apply Hsim.
  Qed.

  Lemma target_op iₜ iₛ fₜ fₛ pcₜ pcₛ :
    ∀ pc dst op regs args v,
    fₜ@pcₜ is <{ dst := @op regs -> pc }> ->
    eval_op op args = Some v ->
    ⊨ regs ↪ₜ args ->
      ⟦ dst ↩ₜ v ⟧ (fₜ, pc) ⟨S iₜ ≲ iₛ⟩ (fₛ, pcₛ) {{ Φ }} ->
      (fₜ, pcₜ) ⟨iₜ ≲ iₛ⟩ (fₛ, pcₛ) {{ Φ }}.
  Proof using Type.
    intros pc dst op regs args v Hpc Hv [ρₜ mₜ] [ρₛ mₛ].
    intros Harg Hsim. unfold_bilogic.
    apply (@fsim_roll Λₜ Λₛ). subst.
    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep.
      eexists.
      eapply (@fsim_unroll Λₜ Λₛ).
      apply Hsim.
  Qed.

  Lemma source_if iₜ iₛ fₜ fₛ pcₜ pcₛ :
    ∀ pc_true pc_false reg v,
    fₛ@pcₛ is <{ if reg then goto pc_true else goto pc_false }> ->
    ⊨ reg ↪ₛ v ->
      (fₜ, pcₜ) ⟨iₜ ≲ S iₛ⟩ (fₛ, if (v =? 0)%Z then pc_true else pc_false) {{ Φ }} ->
      (fₜ, pcₜ) ⟨iₜ ≲ iₛ⟩ (fₛ, pcₛ) {{ Φ }}.
  Proof using Type.
    intros pc_true pc_false reg Hpc Hv [ρₜ mₜ] [ρₛ mₛ].
    intros Harg Hsim. unfold_bilogic.
    apply (@fsim_roll Λₜ Λₛ). subst.
    eapply FSourceSteps.
    - econstructor; eassumption || reflexivity.
    - eapply (@fsim_unroll Λₜ Λₛ).
      apply Hsim.
  Qed.

  Lemma target_if iₜ iₛ fₜ fₛ pcₜ pcₛ :
    ∀ pc_true pc_false reg v,
    fₜ@pcₜ is <{ if reg then goto pc_true else goto pc_false }> ->
    ⊨ reg ↪ₜ v ->
      (fₜ, if (v =? 0)%Z then pc_true else pc_false) ⟨S iₜ ≲ iₛ⟩ (fₛ, pcₛ) {{ Φ }} ->
      (fₜ, pcₜ) ⟨iₜ ≲ iₛ⟩ (fₛ, pcₛ) {{ Φ }}.
  Proof using Type.
    intros pc_true pc_false reg Hpc Hv [ρₜ mₜ] [ρₛ mₛ].
    intros Harg Hsim. unfold_bilogic.
    apply (@fsim_roll Λₜ Λₛ). subst.
    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep.
      eexists.
      eapply (@fsim_unroll Λₜ Λₛ).
      apply Hsim.
  Qed.

End Rules.
