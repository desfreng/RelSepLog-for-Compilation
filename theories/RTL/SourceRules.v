From RSL Require Import Prelude.

From RSL Require Import Simulations.FreeSim.
From RSL Require Import Simulations.FreeSimRules.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.SimRules.

From RSL Require Import Tactics.Memory.

Import RTLNotations.

Section SourceRulesDef.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation fsim := (fsim WfNat WfNat Pₜ Pₛ).

  Notation
    "'[' C ']' st '<{' j ',' i '}=' ss '{{' Q '}}'" :=
    (sim Pₜ Pₛ C st j i ss Q%I)
      (at level 0, no associativity).

  Lemma source_nop C st j i fₛ pcₛ ρₛ Q :
    ∀ pc,
    fₛ@pcₛ is <<{ nop -> pc }>> ->
    ⊢ [C] st <{j, 1+i}= State fₛ pc ρₛ {{ Q }} -∗
      [C] st <{j, i}= State fₛ pcₛ ρₛ {{ Q }}.
  Proof using Type.
    intros pc Hpc.
    unseal. intros ? ? [-> ->] mt ms _ _ H.
    rewrite !(map_empty_union _).

    eapply FSourceSteps.
    - econstructor; eassumption.
    - apply H.
  Qed.

  Lemma source_op C st j i fₛ pcₛ ρₛ Q :
    ∀ pc dst op regs args,
    fₛ@pcₛ is <<{ dst := @op regs -> pc }>> ->
    ρₛ @ regs ⇒ args ->
    ⊢ (∀ v, ⌜eval_op op args = Some v⌟ -∗
            [C] st <{j, 1+i}= State fₛ pc (⟦dst ⇐ v⟧ρₛ) {{ Q }}) -∗
      [C] st <{j, i}= State fₛ pcₛ ρₛ {{ Q }}.
  Proof using Type.
    intros pc dst op regs args Hpc Hargs.
    unseal. intros ? ? [-> ->] mt ms _ _ H.

    destruct (eval_op op args) as [v|] eqn:Hv.
    - eapply FSourceSteps.
      + econstructor; eassumption || reflexivity.
      + rewrite <- (map_union_comm mt) by solve_map_disjoint.
        rewrite <- (map_union_comm ms) by solve_map_disjoint.
        eapply H; auto; solve_map_disjoint.
    - apply FSourceStuck.
      split. { reflexivity. }
      intros Hprog. apply can_progress_must_step in Hprog.
      destruct Hprog as [? Hprog].
      inv Hprog. simregs.
  Qed.

  Lemma source_load C st j i fₛ pcₛ ρₛ Q :
    ∀ pc dst src addr v,
    fₛ@pcₛ is <<{ dst := !src -> pc }>> ->
    ρₛ @ src ⇒ addr ->
    ⊢ addr →ₛ v -∗
      (addr →ₛ v -∗
       [C] st <{j, 1+i}= State fₛ pc (⟦dst ⇐ v⟧ρₛ) {{ Q }}) -∗
      [C] st <{j, i}= State fₛ pcₛ ρₛ {{ Q }}.
  Proof using Type.
    intros pc dst src addr v Hpc Haddr.
    unfold sim; unseal.
    unseal. intros ? ? [-> ->] mt ms _ _ [-> (l & Hloc & ->)].
    rewrite !(map_empty_union _). intros mt ms ? ? H.

    eapply FSourceSteps.
    - eapply exec_Iload with (v := v); try eassumption.
      + subst. simget.
      + reflexivity.
    - rewrite <- (map_union_comm mt) by solve_map_disjoint.
      rewrite <- (map_union_comm ms) by solve_map_disjoint.

      eapply H; auto; try solve_map_disjoint.
      repeat split.
      eexists. split; eassumption || reflexivity.
  Qed.

  Lemma source_store C st j i fₛ pcₛ ρₛ Q :
    ∀ pc dst src addr v old,
    fₛ@pcₛ is <<{ !dst := src -> pc }>> ->
    ρₛ @ dst ⇒ addr ->
    ρₛ @ src ⇒ v ->
    ⊢
      addr →ₛ old -∗
      (addr →ₛ v -∗ [C] st <{j, 1+i}= State fₛ pc ρₛ {{ Q }}) -∗
      [C] st <{j, i}= State fₛ pcₛ ρₛ {{ Q }}.
  Proof using Type.
    intros pc dst src addr v old Hpc Haddr Hv.
    unseal. intros ? ? [-> ->] mt ms _ _ [-> (l & Hloc & ->)].
    rewrite !(map_empty_union _). intros mtP msP ? ? H.

    eapply FSourceSteps.
    - eapply exec_Istore; try eassumption.
      subst.
      erewrite (set_at_some  _ _ _ _ _ Hloc) by simget.
      erewrite alter_union_left by solve_map_disjoint.
      rewrite !alter_singleton.
      reflexivity.
    - subst.
      rewrite <- (map_union_comm mtP) by solve_map_disjoint.
      rewrite <- (map_union_comm msP) by solve_map_disjoint.
      eapply H; auto; try solve_map_disjoint.
      repeat split.
      eexists. split; eassumption || reflexivity.
  Qed.

  Lemma source_if C st j i fₛ pcₛ ρₛ Q :
    ∀ pc_true pc_false reg v pc,
    fₛ@pcₛ is <<{ if reg then goto pc_true else goto pc_false }>> ->
    ρₛ @ reg ⇒ v ->
    (if (v =? 0)%Z then pc_true else pc_false) = pc ->
    ⊢ [C] st <{j, 1+i}= State fₛ pc ρₛ {{ Q }} -∗
      [C] st <{j, i}= State fₛ pcₛ ρₛ {{ Q }}.
  Proof using Type.
    intros pc_true pc_false reg v pc Hpc Hv Hnext_pc.
    unseal. intros ? ? [-> ->] mt ms _ _ H.
    rewrite !(map_empty_union _).

    eapply FSourceSteps.
    - econstructor; eassumption || reflexivity.
    - subst. now apply H.
  Qed.

End SourceRulesDef.
