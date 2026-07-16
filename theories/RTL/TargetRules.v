From RSL Require Import Prelude.

From RSL.Logic Require Export Logic.
From RSL.Simulations Require Export FreeSimRules.
From RSL.RTL Require Export RTL Semantics Notations.

Import RTLNotations.

Section TargetRulesDef.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation sim_lfp := (sim_lfp Pₜ Pₛ).

  Notation
    "'[' C ']' st '<{' j ',' i '}=' ss '{{' Q '}}'" :=
    (sim_lfp C st j i ss Q%I)
      (at level 0,
       st at level 99,
       ss at level 99,
       Q at level 200,
       no associativity).

  Ltac smap :=
    rewrite ?map_union_empty ?map_empty_union ?map_union_assoc;
    try done.

  Lemma target_nop C ct ft pct ρt j i ss Q :
    ∀ pc,
    ft@pct is <<{ nop -> pc }>> ->
    [C] (ct, State ft pc ρt) <{1+j, i}= ss {{ Q }} -∗
    [C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros pc Hpc.
    unseal. intros ? ? [-> ->] ? ? _ _ Hsim. smap.

    apply FTargetSteps.
    - eexists. by econstructor.
    - intros t Hstep. inv Hstep.
      eexists. now apply Hsim.
  Qed.

  Lemma target_ret C ct ft pct ρt j i ss Q :
    ∀ r v,
    ft@pct is <<{ ret r }>> ->
    ρt@r ⇒ v ->
    [C] (ct, ReturnState v) <{1+j, i}= ss {{ Q }} -∗
    [C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros r v Hpc Hr.
    unseal. intros ? ? [-> ->] ? ? _ _ Hsim.
    smap.

    eapply FTargetSteps.
    - eexists. by econstructor.
    - intros t' Hstep. inv Hstep. simregs.
      eexists. by apply Hsim.
  Qed.

  Lemma target_op C ct ft pct ρt j i ss Q :
    ∀ pc dst op regs args v,
    ft@pct is <<{ dst := @op regs -> pc }>> ->
    ρt @ regs ⇒ args ->
    eval_op op args = Some v ->
    [C] (ct, State ft pc (⟦dst ⇐ v⟧ρt)) <{1+j, i}= ss {{ Q }} -∗
    [C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros pc dst op regs args v Hpc Hargs Hv.
    unseal. intros ? ? [-> ->] ? ? _ _ Hsim. smap.

    eapply FTargetSteps.
    - eexists. by econstructor.
    - intros t Hstep. inv Hstep. simregs.
      eexists. now apply Hsim.
  Qed.

  Lemma target_load C ct ft pct ρt j i ss Q :
    ∀ pc dst src l v,
    ft@pct is <<{ dst := !src -> pc }>> ->
    ρt @ src ⇒ VPtr l ->
    (l →ₜ v -∗
     [C] (ct, State ft pc (⟦dst ⇐ v⟧ρt)) <{1+j, i}= ss {{ Q }}) -∗
    l →ₜ v -∗
    [C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros pc dst src l v Hpc Haddr.
    unseal.
    intros ? ? [-> ->] mtP msP _ _ Hsim. smap.
    intros ? ? ? _ [-> ->]. smap.

    decompose_map_disjoint.

    eapply FTargetSteps.
    - eexists. eapply exec_Iload; try eassumption.
      + rewrite get_at_union_right; last done.
        by apply get_at_singl.
      + reflexivity.
    - intros t Hstep.
      inv Hstep as [ | | | ? ? ? ? ? ? ? ? ? ? ? ? ? Hget | | | | | ].
      simregs.
      rewrite get_at_union_right in Hget; last done.
      rewrite get_at_singl in Hget. inv Hget.

      eexists.
      replace msP with (msP ∪ ∅) by smap.
      apply Hsim; smap; by solve_map_disjoint.
  Qed.

  Lemma target_store C ct ft pct ρt j i ss Q :
    ∀ pc dst src l v old,
    ft@pct is <<{ !dst := src -> pc }>> ->
    ρt @ dst ⇒ VPtr l ->
    ρt @ src ⇒ v ->
    (l →ₜ v -∗
     [C] (ct, State ft pc ρt) <{1+j, i}= ss {{ Q }}) -∗
    l →ₜ old -∗
    [C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros pc dst src l v old Hpc Haddr Hv.
    unseal.
    intros ? ? [-> ->] mtP msP _ _ Hsim. smap.
    intros ? ? ? _ [-> ->]. smap.

    decompose_map_disjoint.

    eapply FTargetSteps.
    - eexists. eapply exec_Istore; try eassumption.
      eapply set_at_some.
      rewrite get_at_union_right; last done.
      by apply get_at_singl.
    - intros t Hstep.
      inv Hstep as [ | | | | ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hset | | | | ].
      simregs.
      erewrite set_at_some in Hset.
      + rewrite insert_union_r in Hset; last done.
        rewrite insert_singleton_eq in Hset.
        inv Hset.

        eexists.
        replace msP with (msP ∪ ∅) by smap.
        apply Hsim; smap; by solve_map_disjoint.
      + rewrite get_at_union_right; last done.
        by apply get_at_singl.
  Qed.

  Lemma target_if C ct ft pct ρt j i ss Q :
    ∀ pc_true pc_false reg b,
    ft@pct is <<{ if reg then goto pc_true else goto pc_false }>> ->
    ρt @ reg ⇒ VBool b ->
    let pc := if b then pc_true else pc_false in
    [C] (ct, State ft pc ρt) <{1+j, i}= ss {{ Q }} -∗
    [C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros pc_true pc_false reg b pc Hpc.
    unseal.
    intros ? ? [-> ->] ? ? _ _ Hsim. smap.

    apply FTargetSteps.
    - eexists. by econstructor.
    - intros t Hstep. inv Hstep. simregs.
      eexists. now apply Hsim.
  Qed.

End TargetRulesDef.
