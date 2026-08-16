From RSL Require Import Prelude.

From RSL.RTL Require Import RTL Semantics.
From RSL.RTL.Rules Require Import SourceRules.
From RSL.Logic Require Import Logic.

Import RTLNotations.

Section FailingSourceRulesDef.
  Context {Λt : lang}.
  Let Λs : lang := rtl_lang.
  Context {Pt : prog Λt} {Ps : prog Λs}.
  Context {C : Chain (fsim_lfp WfNat WfNat Pt Ps)}.

  Context (st : istate Λt) (j i : WfNat) (cs : list stackframe)
    (fs : rtl_function) (pcs : node) (ρs : regbank)
    (Q : value Λt -> value Λs -> rProp).

  Lemma source_fail :
    (rtl_fn_code fs) !! pcs = None ->
    True -∗
    [Pt, Ps, C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros Hpc. unseal.
    intros ? ? [-> ->] mt ms _ _ _. smap.
    source_does_UB.
  Qed.

  Lemma source_op_fail pc dst op regs args:
    fs@pcs is <<{ dst := @op regs -> pc }>> ->
    ρs @ regs ⇒ args ->
    eval_op op args = None ->
    True -∗
    [Pt, Ps, C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros Hpc Hargs Hv. unseal.
    intros ? ? [-> ->] mt ms _ _ _. smap.
    source_does_UB.
  Qed.

  Lemma source_call_fail dst sig args pc' :
    fs@pcs is <<{ dst := @call sig args -> pc' }>> ->
    find_fun Ps sig = None ->
    True -∗
    [Pt, Ps, C] st <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros Hpc Hfun. unseal.
    intros ? ? [-> ->] mtP msP _ _ Hsim. smap.
    source_does_UB.
  Qed.

  Lemma source_callstate_fail args:
    length args ≠ length (rtl_fn_regs fs) ->
    True -∗
    [Pt, Ps, C] st <{j, i}= (cs, CallState fs args) {{ Q }}.
  Proof using Type.
    intros Hlen. unseal.
    intros ? ? [-> ->] mt ms _ _ Hsim. smap.
    source_does_UB.
  Qed.
End FailingSourceRulesDef.
