From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Commons.Bilogic.
From RSL Require Import Commons.Logic.

From RSL Require Import Simulation.Sim.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.WP.

(* Set Mangle Names. *)

Import RTLNotations.

Section Rules.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: val -> val -> memory -> memory -> Prop).

  Notation "t '≲' s '{{' Φ '}}'" := (gfp (sim_lfp Pₜ Pₛ Φ) t s).

  Definition sim Φ fₜ pcₜ fₛ pcₛ : bilogic :=
    fun '(ρₜ, mₜ) '(ρₛ, mₛ) =>
      ([], State fₜ pcₜ ρₜ, mₜ) ≲ ([], State fₛ pcₛ ρₛ, mₛ)
        {{ fun '(vₜ, mₜ) '(vₛ, mₛ) => Φ vₜ vₛ mₜ mₛ }}.

  Hint Unfold sim : custom_bilogic.

  Notation "'⟨' t ',' pct '⟩' '≲' '⟨' s ',' pcs '⟩' '{{' Φ '}}'" :=
    (sim Φ t pct s pcs)
      (at level 10,
          no associativity).

  Lemma target_ret fₜ fₛ pcₜ pcₛ : ∀ rₜ vₜ vₛ ρₜ mₜ ρₛ mₛ s',
    fₜ@pcₜ is <{ ret rₜ }> ->
    Pₛ ⊨ ([], State fₛ pcₛ ρₛ, mₛ) ->>* s' ->
    is_final s' = Some (vₛ, mₛ) ->
    Φ vₜ vₛ mₜ mₛ ->
    ⟨ fₜ, pcₜ ⟩ ≲ ⟨ fₛ, pcₛ ⟩ {{ Φ }} (ρₜ, mₜ) (ρₛ, mₛ).
  Proof.
    intros rₜ rₛ vₜ vₛ Hpct Hpcs [ρₜ mₜ] [ρₛ mₛ] Hrt Hrs HΦ.
    unfold_bilogic. step.
    apply BothSteps.
    - do 2 econstructor; eassumption.
    - intros t Ht.
      eexists. split.
      + econstructor; eassumption.
      + inv Ht. step.
        apply BothFinal.
        do 2 eexists; now eauto.
  Qed.

  Lemma both_ret fₜ fₛ pcₜ pcₛ : ∀ rₜ rₛ vₜ vₛ,
    fₜ@pcₜ is <{ ret rₜ }> ->
    fₛ@pcₛ is <{ ret rₛ }> ->
    ⊨ rₜ ↪ₜ vₜ ->
      rₛ ↪ₛ vₛ ->
      ⌜Φ vₜ vₛ⌝ₘ  ->
      ⟨ fₜ, pcₜ ⟩ ≲ ⟨ fₛ, pcₛ ⟩ {{ Φ }}.
  Proof.
    intros rₜ rₛ vₜ vₛ Hpct Hpcs [ρₜ mₜ] [ρₛ mₛ] Hrt Hrs HΦ.
    unfold_bilogic. step.
    apply BothSteps.
    - do 2 econstructor; eassumption.
    - intros t Ht.
      eexists. split.
      + econstructor; eassumption.
      + inv Ht. step.
        apply BothFinal.
        do 2 eexists; now eauto.
  Qed.

  Lemma both_nop fₜ fₛ pcₜ pcₛ : ∀ pcₜ' pcₛ',
    fₜ@pcₜ is <{ nop -> pcₜ' }> ->
    fₛ@pcₛ is <{ nop -> pcₛ' }> ->
    ⊨ ⟨ fₜ, pcₜ' ⟩ ≲ ⟨ fₛ, pcₛ' ⟩ {{ Φ }} ->
    ⟨ fₜ, pcₜ ⟩ ≲ ⟨ fₛ, pcₛ ⟩ {{ Φ }}.
  Proof.
    intros pct' pcs' Hpct Hpcs [ρₜ mₜ] [ρₛ mₛ] H.
    unfold_bilogic. step.
    apply BothSteps.
    - eexists. constructor; eassumption.
    - intros t' Ht.
      eexists. split.
      + constructor; eassumption.
      + now inv Ht.
  Qed.

  Lemma both_op fₜ fₛ pcₜ pcₛ :
    ∀ pcₜ' pcₛ' dstₜ dstₛ opₜ opₛ regsₜ regsₛ argsₜ argsₛ v,
    fₜ@pcₜ is <{ dstₜ := @opₜ regsₜ -> pcₜ' }> ->
    fₛ@pcₛ is <{ dstₛ := @opₛ regsₛ -> pcₛ' }> ->
    eval_op opₜ argsₜ = Some v ->
    eval_op opₛ argsₛ = Some v ->
    ⊨ regsₜ ↪ₜ argsₜ ->
      regsₛ ↪ₛ argsₛ ->
      ⟦ dstₜ ↩ₜ v , dstₛ ↩ₛ v ⟧ ⟨ fₜ, pcₜ' ⟩ ≲  ⟨ fₛ, pcₛ' ⟩ {{ Φ }} ->
      ⟨ fₜ, pcₜ ⟩ ≲  ⟨ fₛ, pcₛ ⟩ {{ Φ }}.
  Proof.
    intros pcₜ' pcₛ' dstₜ dstₛ  opₜ opₛ regsₜ regsₛ argsₜ argsₛ v.
    intros Hpct Hpcs Hevt Hevs [ρₜ mₜ] [ρₛ mₛ] Hargt Hargs Hsim.
    unfold_bilogic. step. subst.
    apply BothSteps.
    - do 2 econstructor; eassumption || reflexivity.
    - intros t' Ht.
      eexists. split.
      + econstructor; eassumption || reflexivity.
      + inv Ht. now apply Hsim.
  Qed.

  Lemma both_load fₜ fₛ pcₜ pcₛ :
    ∀ pcₜ' pcₛ' dstₜ dstₛ rₜ rₛ addrₜ addrₛ v,
    fₜ@pcₜ is <{ dstₜ := !rₜ -> pcₜ' }> ->
    fₛ@pcₛ is <{ dstₛ := !rₛ -> pcₛ' }> ->
    ⊨ rₜ ↪ₜ addrₜ ->
      rₛ ↪ₛ addrₛ ->
      addrₛ →ₛ v ->
      addrₜ →ₜ v ->
      ⟦ dstₜ ↩ₜ v , dstₛ ↩ₛ v ⟧ ⟨ fₜ, pcₜ' ⟩ ≲  ⟨ fₛ, pcₛ' ⟩ {{ Φ }} ->
      ⟨ fₜ, pcₜ ⟩ ≲  ⟨ fₛ, pcₛ ⟩ {{ Φ }}.
  Proof.
    intros pcₜ' pcₛ' dstₜ dstₛ rₜ rₛ addrₜ addrₛ v.
    intros Hpct Hpcs [ρₜ mₜ] [ρₛ mₛ] Hargt Hargs Haddrs Haddrt Hsim.
    unfold_bilogic. step. subst.
    apply BothSteps.
    - do 2 econstructor; eassumption || reflexivity.
    - intros t' Ht.
      eexists. split.
      + econstructor; eassumption || reflexivity.
      + inv Ht. now apply Hsim.
  Qed.

  Lemma both_store fₜ fₛ pcₜ pcₛ :
    ∀ pcₜ' pcₛ' dst rₜ rₛ addrₜ addrₛ v,
    fₜ@pcₜ is <{ dst := !rₜ -> pcₜ' }> ->
    fₛ@pcₛ is <{ dst := !rₛ -> pcₛ' }> ->
    ⊨ rₜ ↪ₜ addrₜ ->
      rₛ ↪ₛ addrₛ ->
      addrₛ →ₛ v ->
      addrₜ →ₜ v ->
      ⟦ dst ↩ₜ v , dst ↩ₛ v ⟧ ⟨ fₜ, pcₜ' ⟩ ≲  ⟨ fₛ, pcₛ' ⟩ {{ Φ }} ->
      ⟨ fₜ, pcₜ ⟩ ≲  ⟨ fₛ, pcₛ ⟩ {{ Φ }}.
  Proof.
    intros pcₜ' pcₛ' dst rₜ rₛ addrₜ addrₛ v.
    intros Hpct Hpcs [ρₜ mₜ] [ρₛ mₛ] Hargt Hargs Haddrs Haddrt Hsim.
    unfold_bilogic. step. subst.
    apply BothSteps.
    - do 2 econstructor; eassumption || reflexivity.
    - intros t' Ht.
      eexists. split.
      + econstructor; eassumption || reflexivity.
      + inv Ht. now apply Hsim.
  Qed.

  Lemma both_if ft fs pct pcs : ∀ pct' pcs',
    ft@pct is <{ nop -> pct' }> ->
    fs@pcs is <{ nop -> pcs' }> ->
    ⊨ ⟨ ft, pct' ⟩ ≲  ⟨ fs, pcs' ⟩ {{ Φ }} ->
    ⟨ ft, pct ⟩ ≲  ⟨ fs, pcs ⟩ {{ Φ }}.
  Proof.
    intros pct' pcs' Hpct Hpcs [ρₜ mₜ] [ρₛ mₛ] H.
    unfold_bilogic. step.
    apply BothSteps.
    - eexists. constructor; now eauto.
    - intros t' Ht.
      eexists. split.
      + constructor; now eauto.
      + now inv Ht.
  Qed.
