From RSL Require Import Prelude.

From RSL.RTL Require Import RTL Semantics.
From RSL.Logic Require Import Logic.

Import RTLNotations.

Section TargetRulesDef.
  Let Λt : lang := rtl_lang.
  Context {Λs : lang}.
  Context {Pt : prog Λt} {Ps : prog Λs}.
  Context {C : Chain (fsim_lfp WfNat WfNat Pt Ps)}.

  Context (σt : list stackframe) (ft : rtl_function) (pct : node) (ρt : regbank)
    (j i : WfNat) (ss : state Λs) (Q : value Λt -> value Λs -> rProp).

  Ltac target_step :=
    repeat intro; subst; unfold sim; unseal;
    intros ? ? [-> ->] ? ? _ _ Hsim;
    intros W mtW msW Hdt Hds HW; smap;
    apply chain_target_step;
    [ eexists; by econstructor
    | intros t' Hstep; inv Hstep; try simregs; eexists; apply Hsim ].

  Lemma target_nop pc:
    ft@pct is <<{ nop -> pc }>> ->
    [Pt, Ps, C] (σt, State ft pc ρt) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (σt, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma target_ret r v:
    ft@pct is <<{ ret r }>> ->
    ρt@r ⇒ v ->
    [Pt, Ps, C] (σt, ReturnState v) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (σt, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma target_op pc dst op regs args v:
    ft@pct is <<{ dst := @op regs -> pc }>> ->
    ρt @ regs ⇒ args ->
    eval_op op args = Some v ->
    [Pt, Ps, C] (σt, State ft pc (⟦dst ⇐ v⟧ρt)) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (σt, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma target_load pc dst src l v:
    ft@pct is <<{ dst := !src -> pc }>> ->
    ρt @ src ⇒ VPtr l ->
    (l →ₜ v -∗
     [Pt, Ps, C] (σt, State ft pc (⟦dst ⇐ v⟧ρt)) <{1+j, i}= ss {{ Q }}) -∗
    l →ₜ v -∗
    [Pt, Ps, C] (σt, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros Hpc Haddr. unfold sim. unseal.
    intros ? ? [-> ->] mtP msP _ _ Hsim.
    intros ? ? ? _ [-> ->].
    intros W mtW msW Hdt Hds HW. smap.

    decompose_map_disjoint.

    eapply chain_target_step.
    - eexists. eapply exec_Iload; try eassumption.
      + rewrite get_at_union_left; last done.
        rewrite get_at_union_right; last done.
        by apply get_at_singl.
      + reflexivity.
    - intros t Hstep.
      inv Hstep as [ | | | ? ? ? ? ? ? ? ? ? ? ? ? ? Hget | | | | | | | ].
      simregs.
      rewrite get_at_union_left in Hget; last done.
      rewrite get_at_union_right in Hget; last done.
      rewrite get_at_singl in Hget. inv Hget.

      eexists.
      replace (msP ∪ msW) with (msP ∪ ∅ ∪ msW) by smap.
      apply Hsim; smap; by solve_map_disjoint.
  Qed.

  Lemma target_store pc dst src l v old:
    ft@pct is <<{ !dst := src -> pc }>> ->
    ρt @ dst ⇒ VPtr l ->
    ρt @ src ⇒ v ->
    (l →ₜ v -∗
     [Pt, Ps, C] (σt, State ft pc ρt) <{1+j, i}= ss {{ Q }}) -∗
    l →ₜ old -∗
    [Pt, Ps, C] (σt, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros Hpc Haddr Hv. unfold sim. unseal.
    intros ? ? [-> ->] mtP msP _ _ Hsim.
    intros ? ? ? _ [-> ->].
    intros W mtW msW Hdt Hds HW. smap.

    decompose_map_disjoint.

    eapply chain_target_step.
    - eexists. eapply exec_Istore; try eassumption.
      eapply update_at_some.
      rewrite get_at_union_left; last done.
      rewrite get_at_union_right; last done.
      by apply get_at_singl.
    - intros t Hstep.
      inv Hstep as [ | | | | ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hset | | | | | | ].
      simregs.
      unfold set_at in Hset.
      erewrite update_at_some in Hset.
      + rewrite insert_union_l in Hset.
        rewrite insert_union_r in Hset; last done.
        rewrite insert_singleton_eq in Hset.
        inv Hset.

        eexists.
        replace (msP ∪ msW) with (msP ∪ ∅ ∪ msW) by smap.
        apply Hsim; smap; by solve_map_disjoint.
      + rewrite get_at_union_left; last done.
        rewrite get_at_union_right; last done.
        by apply get_at_singl.
  Qed.

  Lemma target_alloc pc dst:
    ft@pct is <<{ dst := alloc () -> pc }>> ->
    (∀ l v,
       l →ₜ v -∗
       [Pt, Ps, C] (σt, State ft pc (⟦dst ⇐ VPtr l⟧ρt)) <{1+j, i}= ss {{ Q }}) -∗
    [Pt, Ps, C] (σt, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros Hpc. unfold sim. unseal.
    intros ? ? [-> ->] mt ms _ _ Hsim.
    intros W mtW msW Hdt Hds HW. smap.

    pose (l := fresh (dom (mt ∪ mtW))).
    assert (Hl: l ∉ dom mt ∪ dom mtW).
    { rewrite <-dom_union_L. by apply is_fresh. }
    apply not_elem_of_union in Hl
        as [Hl%not_elem_of_dom HlW%not_elem_of_dom].

    eapply chain_target_step.
    - eexists. eapply exec_Ialloc with (l := l) (v := inhabitant).
      + done.
      + apply alloc_at_is_some. split.
        * done.
        * by apply lookup_union_None.
      + reflexivity.
    - intros t Hstep.
      inv Hstep as [ | | | | | ? ? ? ? ? ? ? ? ? l' v ? Hm | | | | | ].
      apply alloc_at_is_some in Hm as [-> [? ?]%lookup_union_None].

      eexists.
      replace (mt ∪ mtW ∪ {[l' := Allocated v]}) with (mt ∪ {[l' := Allocated v]} ∪ mtW).
      2:{
        rewrite <-!map_union_assoc. f_equal.
        apply map_union_comm. solve_map_disjoint.
      }
      replace (ms ∪ msW) with (ms ∪ ∅ ∪ msW) by smap.
      eapply Hsim; smap; solve_map_disjoint.
  Qed.

  Lemma target_free pc src l v:
    ft@pct is <<{ free src -> pc }>> ->
    ρt @ src ⇒ VPtr l ->
    (freeₜ l -∗
       [Pt, Ps, C]  (σt, State ft pc ρt) <{1+j, i}= ss {{ Q }}) -∗
    l →ₜ v -∗
    [Pt, Ps, C] (σt, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros Hpc Hsrc. unfold sim. unseal.
    intros ? ? [-> ->] mtP msP _ _ Hsim.
    intros ? ? ? _ [-> ->].
    intros W mtW msW Hdt Hds HW. smap.

    decompose_map_disjoint.

    eapply chain_target_step.
    - eexists. eapply exec_Ifree.
      + done.
      + done.
      + unfold free_at. erewrite update_at_some.
        * reflexivity.
        * rewrite get_at_union_left; last done.
          rewrite get_at_union_right; last done.
          by apply get_at_singl.
    - intros t Hstep.
      inv Hstep as [ | | | | | | ? ? ? ? ? ? ? ? ? ? ? Hm | | | | ].
      simregs.
      unfold free_at in Hm.
      erewrite update_at_some in Hm.
      + rewrite insert_union_l in Hm.
        rewrite insert_union_r in Hm; last done.
        rewrite insert_singleton_eq in Hm.
        inv Hm.

        eexists.
        replace (msP ∪ msW) with (msP ∪ ∅ ∪ msW) by smap.
        apply Hsim; smap; by solve_map_disjoint.
      + rewrite get_at_union_left; last done.
        rewrite get_at_union_right; last done.
        by apply get_at_singl.
  Qed.

  Lemma target_if pcT pcF reg b:
    ft@pct is <<{ if reg then goto pcT else goto pcF }>> ->
    ρt @ reg ⇒ VBool b ->
    let pc := if b then pcT else pcF in
    [Pt, Ps, C] (σt, State ft pc ρt) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (σt, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma target_call dst sig args pc' fn vals st:
    ft@pct is <<{ dst := @call sig args -> pc' }>> ->
    find_fun Pt sig = Some fn ->
    ρt@args ⇒ vals ->
    st = Stackframe dst ft pc' ρt ->
    [Pt, Ps, C] (st :: σt, CallState fn vals) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (σt, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma target_callstate args:
    length args = length (rtl_fn_regs ft) ->
    ρt = init_regs (rtl_fn_regs ft) args ->
    pct = rtl_fn_entrypoint ft ->
    [Pt, Ps, C] (σt, State ft pct ρt) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (σt, CallState ft args) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma source_retstate fn dst v:
    [Pt, Ps, C] (σt, State fn pct (⟦dst ⇐ v⟧ρt)) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (Stackframe dst fn pct ρt :: σt, ReturnState v) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

End TargetRulesDef.
