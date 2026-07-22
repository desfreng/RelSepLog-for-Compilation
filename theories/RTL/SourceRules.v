From RSL Require Import Prelude.

From RSL.Simulations Require Export FreeSimRules.
From RSL.RTL Require Export RTL Semantics Notations.
From RSL.Logic Require Export Logic.

Import RTLNotations.

Section SourceRulesDef.
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

  Ltac source_does_UB :=
    hnf;
    match goal with
    | |- fsim_lfp' _ _ _ _ _ _ ?t ?i ?j (?cs, ?ss, ?ms) =>
        let Hpreg := fresh "Hprog" in
        by apply FSourceStuck;
        split;
        [ destruct cs
        |  intros Hprog; apply can_progress_must_step in Hprog;
          destruct Hprog as [? Hprog]; inv Hprog; simregs]
    | _ => fail "Not a fsim goal"
    end.

  Ltac smap :=
    rewrite ?map_union_empty ?map_empty_union ?map_union_assoc;
    try done.

  Ltac source_step :=
    repeat intro; subst; unseal;
    intros ? ? [-> ->] ? ? _ _ Hsim; smap;
    econstructor; [by econstructor|apply Hsim].

  Lemma source_nop C st j i cs fs pcs ρs Q :
    ∀ pc,
    fs@pcs is <<{ nop -> pc }>> ->
    [C] st <{j, 1+i}= (cs, State fs pc ρs) {{ Q }} -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_ret C st j i cs fs pcs ρs Q :
    ∀ r v,
    fs@pcs is <<{ ret r }>> ->
    ρs@r ⇒ v ->
    [C] st <{j, 1+i}= (cs, ReturnState v) {{ Q }} -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_op C st j i cs fs pcs ρs Q :
    ∀ pc dst op regs args v,
    fs@pcs is <<{ dst := @op regs -> pc }>> ->
    ρs @ regs ⇒ args ->
    eval_op op args = Some v ->
    [C] st <{j, 1+i}= (cs, State fs pc (⟦dst ⇐ v⟧ρs)) {{ Q }} -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_op_exploit C st j i cs fs pcs ρs Q :
    ∀ pc dst op regs args,
    fs@pcs is <<{ dst := @op regs -> pc }>> ->
    ρs @ regs ⇒ args ->
    (∀ v,
       ⌜eval_op op args = Some v⌟ -∗
       [C] st <{j, 1+i}= (cs, State fs pc (⟦dst ⇐ v⟧ρs)) {{ Q }}) -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros pc dst op regs args Hpc Hargs.
    unseal.
    intros ? ? [-> ->] mtP msP _ _ Hsim. smap.

    destruct (eval_op op args) as [v|] eqn:Hv; try source_does_UB.
    eapply FSourceSteps.
    - by econstructor.
    - replace mtP with (mtP ∪ ∅) by smap.
      replace msP with (msP ∪ ∅) by smap.
      apply Hsim.
      + apply map_disjoint_empty_l.
      + apply map_disjoint_empty_l.
      + by split.
  Qed.

  Lemma source_load C st j i cs fs pcs ρs Q :
    ∀ pc dst src l vs,
    fs@pcs is <<{ dst := !src -> pc }>> ->
    ρs @ src ⇒ VPtr l ->
    (l →ₛ vs -∗
     [C] st <{j, i}= (cs, State fs pc (⟦dst ⇐ vs⟧ρs)) {{ Q }}) -∗
    l →ₛ vs -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros pc dst src l vs Hpc Haddr.
    unseal.
    intros ? ? [-> ->] mtS msS _ _ Hsim. smap.
    intros ? ? _ Hdij [-> ->].
    decompose_map_disjoint.

    eapply FSourceSteps.
    {
      eapply exec_Iload with (v := vs); try done.
      rewrite get_at_union_right; auto.
      rewrite get_at_singl; auto.
    }

    eapply Hsim; smap; by solve_map_disjoint.
  Qed.

  Lemma source_load_exploit I E C st j i cs fs pcs ρs Q :
    ∀ pc dst src addr valt,
    fs@pcs is <<{ dst := !src -> pc }>> ->
    ρs @ src ⇒ addr ->
    same_val I valt addr ->
    (∀ ls, addr = VPtr ls -> ls ∉ dom E) ->
    (∀ lt ls vt vs,
       ⌜addr = VPtr ls⌟ -∗
       ⌜valt = VPtr lt⌟ -∗
       lt →ₜ vt -∗
       ls →ₛ vs -∗
       ⌜same_val I vt vs⌟ -∗
       mem_inj I ({[ (ls, lt) ]} ∪ E) -∗
       [C] st <{j, 1+i}= (cs, State fs pc (⟦dst ⇐ vs⟧ρs)) {{ Q }}) -∗
    mem_inj I E -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros pc dst src addr valt Hpc Haddr Hrel HnE.
    unseal.
    intros ? ? [-> ->] mtS msS _ _ Hsim. smap.
    intros mtI msI HtI HsI Hinj.
    destruct addr as [ | | ls | ]; try source_does_UB.
    destruct valt as [ | | lt | ]; try contradiction.

    pose proof (inj_exploit I E _ _ Hrel (HnE _ eq_refl)) as H.
    unseal_in H.
    apply (H ∅ ∅) in Hinj; try (apply map_disjoint_empty_r || easy).
    clear H.
    destruct Hinj as (vt & vs & Hinj).
    rewrite !map_empty_union in Hinj.
    destruct Hinj as (? & ? & ? & ? & ? & ? & <- & <- & [-> ->] & Hinj).
    destruct Hinj as (? & ? & ? & ? & ? & ? & <- & <- & [-> ->] & Hinj).
    destruct Hinj as (? & ? & mtI & msI & _ & _ & <- & <- & [[-> ->] Hsame] & Hinj).
    simpl in Hsame.
    smap.

    decompose_map_disjoint.

    eapply FSourceSteps.
    {
      eapply exec_Iload with (v := vs); try done.
      rewrite get_at_union_left; last done.
      rewrite get_at_union_right; last done.
      by apply get_at_singl.
    }

    simpl in Hsim.
    replace (mtS ∪ {[lt := vt]} ∪ mtI) with (mtS ∪ ∅ ∪ ∅ ∪ {[lt := vt]} ∪ ∅ ∪ ∅ ∪ mtI)
      by smap.
    replace (msS ∪ {[ls := vs]} ∪ msI) with (msS ∪ ∅ ∪ ∅ ∪ ∅ ∪ {[ls := vs]} ∪ ∅ ∪ msI)
      by smap.

    eapply Hsim; smap; by solve_map_disjoint.
  Qed.

  Lemma source_store C st j i cs fs pcs ρs Q :
    ∀ pc dst src v l old,
    fs@pcs is <<{ !dst := src -> pc }>> ->
    ρs @ dst ⇒ VPtr l ->
    ρs @ src ⇒ v ->
    (l →ₛ v -∗
     [C] st <{j, i}= (cs, State fs pc ρs) {{ Q }}) -∗
    l →ₛ old -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros pc dst src v l old Hpc Haddr Hsrc.
    unseal.
    intros ? ? [-> ->] mtS msS _ _ Hsim. smap.
    intros ? ? _ Hdij [-> ->].
    decompose_map_disjoint.

    eapply FSourceSteps.
    {
      eapply exec_Istore with (v := v); try done.
      erewrite set_at_some.
      - rewrite insert_union_r; last done.
        rewrite insert_singleton_eq.
        reflexivity.
      - rewrite get_at_union_right; last done.
        by apply get_at_singl.
    }

    eapply Hsim; smap; by solve_map_disjoint.
  Qed.

  Lemma source_store_exploit I E C st j i cs fs pcs ρs Q :
    ∀ pc dst src v addr valt,
    fs@pcs is <<{ !dst := src -> pc }>> ->
    ρs @ dst ⇒ addr ->
    ρs @ src ⇒ v ->
    same_val I valt addr ->
    (∀ ls, addr = VPtr ls -> ls ∉ dom E) ->
    (∀ lt ls vt,
       ⌜addr = VPtr ls⌟ -∗
       ⌜valt = VPtr lt⌟ -∗
       lt →ₜ vt -∗
       ls →ₛ v -∗
       mem_inj I ({[ (ls, lt) ]} ∪ E) -∗
       [C] st <{j, 1+i}= (cs, State fs pc ρs) {{ Q }}) -∗
    mem_inj I E -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros pc dst src v addr valt Hpc Haddr Hsrc Hrel HnE.
    unseal.
    intros ? ? [-> ->] mtS msS _ _ Hsim. smap.
    intros mtI msI HtI HsI Hinj.
    destruct addr as [ | | ls | ]; try source_does_UB.
    destruct valt as [ | | lt | ]; try contradiction.

    pose proof (inj_exploit I E _ _ Hrel (HnE _ eq_refl)) as H.
    unseal_in H.
    apply (H ∅ ∅) in Hinj; try (apply map_disjoint_empty_r || easy).
    clear H.
    destruct Hinj as (vt & vs & Hinj).
    rewrite !map_empty_union in Hinj.
    destruct Hinj as (? & ? & ? & ? & ? & ? & <- & <- & [-> ->] & Hinj).
    destruct Hinj as (? & ? & ? & ? & ? & ? & <- & <- & [-> ->] & Hinj).
    destruct Hinj as (? & ? & mtI & msI & _ & _ & <- & <- & [[-> ->] Hsame] & Hinj).
    simpl in Hsame.
    smap.

    decompose_map_disjoint.

    eapply FSourceSteps.
    {
      eapply exec_Istore with (v := v); try done.
      erewrite set_at_some.
      - rewrite insert_union_l insert_union_r; last done.
        rewrite insert_singleton_eq.
        reflexivity.
      - rewrite get_at_union_left; last done.
        rewrite get_at_union_right; last done.
        by apply get_at_singl.
    }

    replace (mtS ∪ {[lt := vt]} ∪ mtI) with (mtS ∪ ∅ ∪ ∅ ∪ {[lt := vt]} ∪ ∅ ∪ mtI)
      by smap.
    replace (msS ∪ {[ls := v]} ∪ msI) with (msS ∪ ∅ ∪ ∅ ∪ ∅ ∪ {[ls := v]} ∪ msI)
      by smap.

    eapply Hsim; smap; by solve_map_disjoint.
  Qed.

  Lemma source_if C st j i cs fs pcs ρs Q :
    ∀ pc_true pc_false reg b,
    fs@pcs is <<{ if reg then goto pc_true else goto pc_false }>> ->
    ρs @ reg ⇒ VBool b ->
    [C] st <{j, 1+i}= (cs, State fs (if b then pc_true else pc_false) ρs) {{ Q }} -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_if_exploit C st j i cs fs pcs ρs Q :
    ∀ pc_true pc_false reg v,
    fs@pcs is <<{ if reg then goto pc_true else goto pc_false }>> ->
    ρs @ reg ⇒ v ->
    (∀ b pc,
       ⌜v = VBool b⌟ -∗
       ⌜pc = if b then pc_true else pc_false⌟ -∗
       [C] st <{j, 1+i}= (cs, State fs pc ρs) {{ Q }}) -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros pc_true pc_false reg v Hpc Hv.
    unseal.
    intros ? ? [-> ->] mtP msP _ _ Hsim.
    destruct v as [ | b | | ]; try source_does_UB.
    eapply FSourceSteps.
    { by econstructor. }
    replace (∅ ∪ mtP) with (mtP ∪ ∅ ∪ ∅) by smap.
    replace (∅ ∪ msP) with (msP ∪ ∅ ∪ ∅) by smap.
    apply Hsim with b.
    - apply map_disjoint_empty_l.
    - apply map_disjoint_empty_l.
    - by split.
    - smap. apply map_disjoint_empty_l.
    - smap. apply map_disjoint_empty_l.
    - by split.
  Qed.

  Lemma source_call C st j i cs fs pcs ρs Q :
    ∀ dst sig args pc' fn vals,
    fs@pcs is <<{ dst := @call sig args -> pc' }>> ->
    find_fun Pₛ sig = Some fn ->
    ρs@args ⇒ vals ->
    [C] st <{j, 1+i}= (Stackframe dst fs pc' ρs :: cs, CallState fn vals) {{ Q }} -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_call_exploit C st j i cs fs pcs ρs Q :
    ∀ dst sig args pc',
    fs@pcs is <<{ dst := @call sig args -> pc' }>> ->
    (∀ fn vals,
       ⌜find_fun Pₛ sig = Some fn⌟ -∗
       ⌜ρs@args ⇒ vals⌟ -∗
       [C] st <{j, 1+i}= (Stackframe dst fs pc' ρs :: cs, CallState fn vals) {{ Q }}) -∗
    [C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros dst sig args pc' Hpc.
    unseal.
    intros ? ? [-> ->] mtP msP _ _ Hsim. smap.
    destruct (find_fun Pₛ sig) as [fn|] eqn:Hfn; try source_does_UB.

    eapply FSourceSteps. { by econstructor. }

    replace mtP with (mtP ∪ ∅ ∪ ∅) by smap.
    replace msP with (msP ∪ ∅ ∪ ∅) by smap.

    eapply Hsim.
    - apply map_disjoint_empty_l.
    - apply map_disjoint_empty_l.
    - by split.
    - smap. apply map_disjoint_empty_l.
    - smap. apply map_disjoint_empty_l.
    - by split.
  Qed.

  Lemma source_callstate C st j i cs fs args Q :
    ∀ ρs pc,
    length args = length (fn_regs fs) ->
    ρs = init_regs fs args ->
    pc = fn_entrypoint fs ->
    [C] st <{j, 1+i}= (cs, State fs pc ρs) {{ Q }} -∗
    [C] st <{j, i}= (cs, CallState fs args) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_callstate_exploit C st j i cs fs args Q :
    (∀ ρs pc,
       ⌜length args = length (fn_regs fs)⌟ -∗
       ⌜ρs = init_regs fs args⌟ -∗
       ⌜pc = fn_entrypoint fs⌟ -∗
       [C] st <{j, 1+i}= (cs, State fs pc ρs) {{ Q }}) -∗
    [C] st <{j, i}= (cs, CallState fs args) {{ Q }}.
  Proof using Type.
    unseal.
    intros ? ? [-> ->] mt ms _ _ Hsim. smap.
    destruct (decide (length args = length (fn_regs fs))) as [Heq | Hneq];
      try source_does_UB.

    eapply FSourceSteps. { by econstructor. }

    replace mt with (mt ∪ ∅ ∪ ∅ ∪ ∅) by smap.
    replace ms with (ms ∪ ∅ ∪ ∅ ∪ ∅) by smap.

    apply Hsim.
    - apply map_disjoint_empty_l.
    - apply map_disjoint_empty_l.
    - by split.
    - smap. apply map_disjoint_empty_l.
    - smap. apply map_disjoint_empty_l.
    - by split.
    - smap. apply map_disjoint_empty_l.
    - smap. apply map_disjoint_empty_l.
    - by split.
  Qed.

  Lemma source_retstate C st j i cs v Q :
    ∀ fn pc ρs dst,
    [C] st <{j, 1+i}= (cs, State fn pc (⟦dst ⇐ v⟧ρs)) {{ Q }} -∗
    [C] st <{j, i}= (Stackframe dst fn pc ρs :: cs, ReturnState v) {{ Q }}.
  Proof using Type. by source_step. Qed.

End SourceRulesDef.
