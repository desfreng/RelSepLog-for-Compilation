From RSL Require Import Prelude.

From RSL.RTL Require Import RTL Semantics.
From RSL.Logic Require Import Logic.

Import RTLNotations.

Ltac source_does_UB :=
  unfold sim_lfp; cbv [rPropDef.rProp_holds];
  match goal with
  | |- elem _ ?Q ?t ?j ?i (?cs, ?ss, ?ms) =>
      let Hpreg := fresh "Hprog" in
      by eapply chain_stuck; split;
      [ destruct cs
      | intros ? Hprog;
        apply can_progress_must_step in Hprog;
        destruct Hprog as [? Hprog]; inv Hprog; simregs
      ]
  | _ => fail "Not a fsim goal"
  end.

Ltac source_step :=
  repeat intro; subst; unseal;
  intros ? ? [-> ->] ? ? _ _ Hsim; smap;
  eapply chain_source_step; [by econstructor|apply Hsim].

Section SourceRulesDef.
  Context {Λt : lang}.
  Let Λs : lang := rtl_lang.
  Context {Pt : prog Λt} {Ps : prog Λs}.
  Context {C : Chain (fsim_lfp WfNat WfNat Pt Ps)}.

  Context (st : state Λt) (j i : WfNat) (σs : list stackframe)
    (fs : rtl_function) (pcs : node) (ρs : regbank)
    (Q : value Λt -> value Λs -> rProp).

  Lemma source_nop pc:
    fs@pcs is <<{ nop -> pc }>> ->
    [Pt, Ps, C] st <{j, 1+i}= (σs, State fs pc ρs) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (σs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_nop_noinc pc:
    fs@pcs is <<{ nop -> pc }>> ->
    [Pt, Ps, C] st <{j, i}= (σs, State fs pc ρs) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (σs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_ret r v:
    fs@pcs is <<{ ret r }>> ->
    ρs@r ⇒ v ->
    [Pt, Ps, C] st <{j, 1+i}= (σs, ReturnState v) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (σs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_op pc dst op regs args v:
    fs@pcs is <<{ dst := @op regs -> pc }>> ->
    ρs @ regs ⇒ args ->
    eval_op op args = Some v ->
    [Pt, Ps, C] st <{j, 1+i}= (σs, State fs pc (⟦dst ⇐ v⟧ρs)) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (σs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_load pc dst src l vs:
    fs@pcs is <<{ dst := !src -> pc }>> ->
    ρs @ src ⇒ VPtr l ->
    (l →ₛ vs -∗
     [Pt, Ps, C] st <{j, 1+i}= (σs, State fs pc (⟦dst ⇐ vs⟧ρs)) {{ Q }}) -∗
    l →ₛ vs -∗
    [Pt, Ps, C] st <{j, i}= (σs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros Hpc Haddr. unseal.
    intros ? ? [-> ->] mtS msS _ _ Hsim. smap.
    intros ? ? _ Hdij [-> ->].
    decompose_map_disjoint.

    eapply chain_source_step.
    - eapply exec_Iload with (v := vs); try done.
      rewrite get_at_union_right; auto.
      rewrite get_at_singl; auto.
    - eapply Hsim; smap; by solve_map_disjoint.
  Qed.

  Lemma source_store pc dst src v l old:
    fs@pcs is <<{ !dst := src -> pc }>> ->
    ρs @ dst ⇒ VPtr l ->
    ρs @ src ⇒ v ->
    (l →ₛ v -∗
     [Pt, Ps, C] st <{j, 1+i}= (σs, State fs pc ρs) {{ Q }}) -∗
    l →ₛ old -∗
    [Pt, Ps, C] st <{j, i}= (σs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros Hpc Haddr Hsrc. unseal.
    intros ? ? [-> ->] mtS msS _ _ Hsim. smap.
    intros ? ? _ Hdij [-> ->].
    decompose_map_disjoint.

    eapply chain_source_step.
    - eapply exec_Istore with (v := v); try done.
      unfold set_at. erewrite update_at_some.
      + rewrite insert_union_r; last done.
        rewrite insert_singleton_eq.
        reflexivity.
      + rewrite get_at_union_right; last done.
        by apply get_at_singl.
    - eapply Hsim; smap; by solve_map_disjoint.
  Qed.

  Lemma source_alloc pc dst v:
    fs@pcs is <<{ dst := alloc () -> pc }>> ->
    (∀ l,
       l →ₛ v -∗
       [Pt, Ps, C] st <{j, 1+i}= (σs, State fs pc (⟦dst ⇐ VPtr l⟧ρs)) {{ Q }}) -∗
    [Pt, Ps, C] st <{j, i}= (σs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros Hpc. unseal.
    intros ? ? [-> ->] mtS msS _ _ Hsim. smap.

    eapply chain_source_step.
    - eapply exec_Ialloc.
      + done.
      + rewrite alloc_at_is_some. split.
        * reflexivity.
        * apply not_elem_of_dom, is_fresh.
      + reflexivity.
    - replace mtS with (mtS ∪ ∅) by smap.
      eapply Hsim.
      + solve_map_disjoint.
      + apply map_disjoint_singleton_l, not_elem_of_dom, is_fresh.
      + by split.
  Qed.

  Lemma source_free pc src l v:
    fs@pcs is <<{ free src -> pc }>> ->
    ρs @ src ⇒ VPtr l ->
    (freeₛ l -∗
       [Pt, Ps, C] st <{j, 1+i}= (σs, State fs pc ρs) {{ Q }}) -∗
    l →ₛ v -∗
    [Pt, Ps, C] st <{j, i}= (σs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros Hpc Hsrc. unseal.
    intros ? ? [-> ->] mtS msS _ _ Hsim. smap.
    intros ? ? _ Hdij [-> ->].
    decompose_map_disjoint.

    eapply chain_source_step.
    - eapply exec_Ifree.
      + done.
      + done.
      + unfold free_at. erewrite update_at_some.
        * rewrite insert_union_r; last done.
          rewrite insert_singleton_eq.
          reflexivity.
        * rewrite get_at_union_right; last done.
          by apply get_at_singl.
    - eapply Hsim; smap; by solve_map_disjoint.
  Qed.

  Lemma source_if pcT pcF reg b:
    fs@pcs is <<{ if reg then goto pcT else goto pcF }>> ->
    ρs @ reg ⇒ VBool b ->
    let pc := if b then pcT else pcF in
    [Pt, Ps, C] st <{j, 1+i}= (σs, State fs pc ρs) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (σs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_call dst sig args pc' fn vals ss:
    fs@pcs is <<{ dst := @call sig args -> pc' }>> ->
    find_fun Ps sig = Some fn ->
    ρs@args ⇒ vals ->
    ss = Stackframe dst fs pc' ρs ->
    [Pt, Ps, C] st <{j, 1+i}= (ss :: σs, CallState fn vals) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (σs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_callstate args:
    length args = length (rtl_fn_regs fs) ->
    ρs = init_regs (rtl_fn_regs fs) args ->
    pcs = rtl_fn_entrypoint fs ->
    [Pt, Ps, C] st <{j, 1+i}= (σs, State fs pcs ρs) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (σs, CallState fs args) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_retstate v fn pc dst:
    [Pt, Ps, C] st <{j, 1+i}= (σs, State fn pc (⟦dst ⇐ v⟧ρs)) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (Stackframe dst fn pc ρs :: σs, ReturnState v) {{ Q }}.
  Proof using Type. by source_step. Qed.

End SourceRulesDef.
