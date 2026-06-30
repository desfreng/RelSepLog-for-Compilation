From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.FreeSim.
From RSL Require Import Simulations.FreeSimRules.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.SimRules.

From RSL Require Import Tactics.Memory.

Import RTLNotations.

Section TargetRulesDef.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation fsim := (fsim WfNat WfNat Pₜ Pₛ).

  Notation
    "'[' C ']' st '<{' j ',' i '}=' ss '{{' Q '}}'" :=
    (sim Pₜ Pₛ C st j i ss Q%I)
      (at level 0, no associativity).

  Lemma target_nop C fₜ pcₜ ρₜ j i ss Q :
    ∀ pc,
    fₜ@pcₜ is <<{ nop -> pc }>> ->
    ⊢ [C] State fₜ pc ρₜ <{1+j, i}= ss {{ Q }} -∗
      [C] State fₜ pcₜ ρₜ <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros pc Hpc.
    unseal. intros ? ? [-> ->] mt ms _ _ H.
    rewrite !(map_empty_union _).

    eapply FTargetSteps.
    - eexists. econstructor; eassumption.
    - intros t Hstep. inv Hstep.
      eexists. now apply H.
  Qed.

  Lemma target_op C fₜ pcₜ ρₜ j i ss Q :
    ∀ pc dst op regs args v,
    fₜ@pcₜ is <<{ dst := @op regs -> pc }>> ->
    ρₜ @ regs ⇒ args ->
    eval_op op args = Some v ->
    ⊢ [C] State fₜ pc (⟦dst ⇐ v⟧ρₜ) <{1+j, i}= ss {{ Q }} -∗
      [C] State fₜ pcₜ ρₜ <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros pc dst op regs args v Hpc Hargs Hv.
    unseal. intros ? ? [-> ->] mt ms _ _ H.
    rewrite !(map_empty_union _).

    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep. simregs.
      eexists. now apply H.
  Qed.

  Lemma target_load C fₜ pcₜ ρₜ j i ss Q :
    ∀ pc dst src addr v,
    fₜ@pcₜ is <<{ dst := !src -> pc }>> ->
    ρₜ @ src ⇒ addr ->
    ⊢ addr →ₜ v -∗
      (addr →ₜ v -∗
       [C] State fₜ pc (⟦dst ⇐ v⟧ρₜ) <{1+j, i}= ss {{ Q }}) -∗
      [C] State fₜ pcₜ ρₜ <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros pc dst src addr v Hpc Haddr.
    unseal. intros ? ? [-> ->] ? ? _ _ [(l & Hloc & ->) ->].
    rewrite !(map_empty_union _). intros mt ms ? ? H.

    eapply FTargetSteps.
    - eexists. eapply exec_Iload; try eassumption.
      + subst. now simget.
      + reflexivity.
    - subst.
      intros t Hstep.
      inv Hstep. simregs. simget. subst.

      eexists.
      rewrite <- (map_union_comm mt) by solve_map_disjoint.
      rewrite <- (map_union_comm ms) by solve_map_disjoint.

      eapply H; auto; try solve_map_disjoint.
      repeat split.
      eexists. split; eassumption || reflexivity.
  Qed.

  Lemma target_store C fₜ pcₜ ρₜ j i ss Q :
    ∀ pc dst src addr v old,
    fₜ@pcₜ is <<{ !dst := src -> pc }>> ->
    ρₜ @ dst ⇒ addr ->
    ρₜ @ src ⇒ v ->
    ⊢ addr →ₜ old -∗
      (addr →ₜ v -∗
       [C] State fₜ pc ρₜ <{1+j, i}= ss {{ Q }}) -∗
      [C] State fₜ pcₜ ρₜ <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros pc dst src addr v old Hpc Haddr Hv.
    unseal. intros ? ? [-> ->] ? ? _ _ [(l & Hloc & ->) ->].
    rewrite !(map_empty_union _). intros mt ms ? ? H.

    eapply FTargetSteps.
    - eexists. eapply exec_Istore; try eassumption.
      subst.
      erewrite (set_at_some  _ _ _ _ _ Hloc) by simget.
      erewrite alter_union_left by solve_map_disjoint.
      now rewrite alter_singleton.
    - intros t Hstep. inv Hstep. simregs.
      erewrite (set_at_some  _ _ _ _ _ Hloc) in * by simget.
      erewrite alter_union_left in * by solve_map_disjoint.
      erewrite alter_singleton in *.
      erewrite inj_some in *.
      subst.

      eexists.
      rewrite <- (map_union_comm mt) by solve_map_disjoint.
      rewrite <- (map_union_comm ms) by solve_map_disjoint.
      eapply H; auto; try solve_map_disjoint.
      repeat split.
      eexists. split; eassumption || reflexivity.
  Qed.

  Lemma target_if C fₜ pcₜ ρₜ j i ss Q :
    ∀ pc_true pc_false reg v pc,
    fₜ@pcₜ is <<{ if reg then goto pc_true else goto pc_false }>> ->
    ρₜ @ reg ⇒ v ->
    (if (v =? 0)%Z then pc_true else pc_false) = pc ->
    ⊢ [C] State fₜ pc ρₜ <{1+j, i}= ss {{ Q }} -∗
      [C] State fₜ pcₜ ρₜ <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros pc_true pc_false reg v pc Hpc Hv Hnext_pc.
    unseal. intros ? ? [-> ->] mt ms _ _ H.
    rewrite !(map_empty_union _).

    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep. simregs.
      eexists. now apply H.
  Qed.

End TargetRulesDef.
