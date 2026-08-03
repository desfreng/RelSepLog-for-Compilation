From RSL Require Import Prelude.

From RSL.RTL Require Import RTL Semantics.
From RSL.Logic Require Import Logic.

Import RTLNotations.

Section TargetRulesDef.
  Let Λt : lang := rtl_lang.
  Context {Λs : lang}.
  Context {Pt : prog Λt} {Ps : prog Λs}.
  Context {C : Chain (fsim_lfp WfNat WfNat Pt Ps)}.

  Context (ct : list stackframe) (ft : rtl_function) (pct : node) (ρt : regbank)
    (j i : WfNat) (ss : pstate Λs) (Q : value Λt -> value Λs -> rProp).

  Ltac target_step :=
    repeat intro; subst; unseal; intros ? ? [-> ->] ? ? _ _ Hsim;
    smap; apply FTargetSteps;
    [ eexists; by econstructor
    | intros t' Hstep; inv Hstep; try simregs; eexists; apply Hsim ].

  Lemma target_nop pc:
    ft@pct is <<{ nop -> pc }>> ->
    [Pt, Ps, C] (ct, State ft pc ρt) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma target_ret r v:
    ft@pct is <<{ ret r }>> ->
    ρt@r ⇒ v ->
    [Pt, Ps, C] (ct, ReturnState v) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma target_op pc dst op regs args v:
    ft@pct is <<{ dst := @op regs -> pc }>> ->
    ρt @ regs ⇒ args ->
    eval_op op args = Some v ->
    [Pt, Ps, C] (ct, State ft pc (⟦dst ⇐ v⟧ρt)) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma target_load pc dst src l v:
    ft@pct is <<{ dst := !src -> pc }>> ->
    ρt @ src ⇒ VPtr l ->
    (l →ₜ v -∗
     [Pt, Ps, C] (ct, State ft pc (⟦dst ⇐ v⟧ρt)) <{1+j, i}= ss {{ Q }}) -∗
    l →ₜ v -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros Hpc Haddr. unseal.
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

  Lemma target_store pc dst src l v old:
    ft@pct is <<{ !dst := src -> pc }>> ->
    ρt @ dst ⇒ VPtr l ->
    ρt @ src ⇒ v ->
    (l →ₜ v -∗
     [Pt, Ps, C] (ct, State ft pc ρt) <{1+j, i}= ss {{ Q }}) -∗
    l →ₜ old -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros Hpc Haddr Hv. unseal.
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

  Lemma target_if pcT pcF reg b:
    ft@pct is <<{ if reg then goto pcT else goto pcF }>> ->
    ρt @ reg ⇒ VBool b ->
    let pc := if b then pcT else pcF in
    [Pt, Ps, C] (ct, State ft pc ρt) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma target_call dst sig args pc' fn vals st:
    ft@pct is <<{ dst := @call sig args -> pc' }>> ->
    find_fun Pt sig = Some fn ->
    ρt@args ⇒ vals ->
    st = Stackframe dst ft pc' ρt ->
    [Pt, Ps, C] (st :: ct, CallState fn vals) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma target_callstate args:
    length args = length (fn_regs ft) ->
    ρt = init_regs ft args ->
    pct = fn_entrypoint ft ->
    [Pt, Ps, C] (ct, State ft pct ρt) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (ct, CallState ft args) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

  Lemma source_retstate fn dst v:
    [Pt, Ps, C] (ct, State fn pct (⟦dst ⇐ v⟧ρt)) <{1+j, i}= ss {{ Q }} -∗
    [Pt, Ps, C] (Stackframe dst fn pct ρt :: ct, ReturnState v) <{j, i}= ss {{ Q }}.
  Proof using Type. by target_step. Qed.

End TargetRulesDef.
