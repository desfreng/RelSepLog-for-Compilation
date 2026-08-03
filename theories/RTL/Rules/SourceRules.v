From RSL Require Import Prelude.

From RSL.RTL Require Import RTL Semantics.
From RSL.Logic Require Import Logic.

Import RTLNotations.

Section SourceRulesDef.
  Context {Λt : lang}.
  Let Λs : lang := rtl_lang.
  Context {Pt : prog Λt} {Ps : prog Λs}.
  Context {C : Chain (fsim_lfp WfNat WfNat Pt Ps)}.

  Context (st : pstate Λt) (j i : WfNat) (cs : list stackframe)
    (fs : rtl_function) (pcs : node) (ρs : regbank)
    (Q : value Λt -> value Λs -> rProp).

  Ltac source_step :=
    repeat intro; subst; unseal;
    intros ? ? [-> ->] ? ? _ _ Hsim; smap;
    econstructor; [by econstructor|apply Hsim].

  Lemma source_nop pc:
    fs@pcs is <<{ nop -> pc }>> ->
    [Pt, Ps, C] st <{j, 1+i}= (cs, State fs pc ρs) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_ret r v:
    fs@pcs is <<{ ret r }>> ->
    ρs@r ⇒ v ->
    [Pt, Ps, C] st <{j, 1+i}= (cs, ReturnState v) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_op pc dst op regs args v:
    fs@pcs is <<{ dst := @op regs -> pc }>> ->
    ρs @ regs ⇒ args ->
    eval_op op args = Some v ->
    [Pt, Ps, C] st <{j, 1+i}= (cs, State fs pc (⟦dst ⇐ v⟧ρs)) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_load pc dst src l vs:
    fs@pcs is <<{ dst := !src -> pc }>> ->
    ρs @ src ⇒ VPtr l ->
    (l →ₛ vs -∗
     [Pt, Ps, C] st <{j, i}= (cs, State fs pc (⟦dst ⇐ vs⟧ρs)) {{ Q }}) -∗
    l →ₛ vs -∗
    [Pt, Ps, C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros Hpc Haddr. unseal.
    intros ? ? [-> ->] mtS msS _ _ Hsim. smap.
    intros ? ? _ Hdij [-> ->].
    decompose_map_disjoint.

    eapply FSourceSteps.
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
     [Pt, Ps, C] st <{j, i}= (cs, State fs pc ρs) {{ Q }}) -∗
    l →ₛ old -∗
    [Pt, Ps, C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros Hpc Haddr Hsrc. unseal.
    intros ? ? [-> ->] mtS msS _ _ Hsim. smap.
    intros ? ? _ Hdij [-> ->].
    decompose_map_disjoint.

    eapply FSourceSteps.
    - eapply exec_Istore with (v := v); try done.
      erewrite set_at_some.
      + rewrite insert_union_r; last done.
        rewrite insert_singleton_eq.
        reflexivity.
      + rewrite get_at_union_right; last done.
        by apply get_at_singl.
    - eapply Hsim; smap; by solve_map_disjoint.
  Qed.

  Lemma source_if pcT pcF reg b:
    fs@pcs is <<{ if reg then goto pcT else goto pcF }>> ->
    ρs @ reg ⇒ VBool b ->
    [Pt, Ps, C] st <{j, 1+i}= (cs, State fs (if b then pcT else pcF) ρs) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_call dst sig args pc' fn vals:
    fs@pcs is <<{ dst := @call sig args -> pc' }>> ->
    find_fun Ps sig = Some fn ->
    ρs@args ⇒ vals ->
    [Pt, Ps, C] st <{j, 1+i}= (Stackframe dst fs pc' ρs :: cs, CallState fn vals) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_callstate args:
    length args = length (fn_regs fs) ->
    ρs = init_regs fs args ->
    pcs = fn_entrypoint fs ->
    [Pt, Ps, C] st <{j, 1+i}= (cs, State fs pcs ρs) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (cs, CallState fs args) {{ Q }}.
  Proof using Type. by source_step. Qed.

  Lemma source_retstate v fn pc dst:
    [Pt, Ps, C] st <{j, 1+i}= (cs, State fn pc (⟦dst ⇐ v⟧ρs)) {{ Q }} -∗
    [Pt, Ps, C] st <{j, i}= (Stackframe dst fn pc ρs :: cs, ReturnState v) {{ Q }}.
  Proof using Type. by source_step. Qed.

End SourceRulesDef.
