From RSL Require Import Prelude.

From RSL.RTL Require Import RTL Semantics.
From RSL.Logic Require Import Logic.

From RSL.RTL.Rules Require Import CallBind Hoare.
From RSL.RTL.Rules Require Import TargetRules SourceRules ExploitSourceRules.

Import RTLNotations.

Section SyncRulesDef.
  Let Λt : lang := rtl_lang.
  Let Λs : lang := rtl_lang.
  Context {Pt : prog Λt} {Ps : prog Λs}.
  Context {C : Chain (fsim_lfp WfNat WfNat Pt Ps)}.

  Implicit Types (ct : list stackframe) (ft : rtl_function) (pct : node) (ρt : regbank).
  Implicit Types (j i : WfNat).
  Implicit Types (cs : list stackframe) (fs : rtl_function) (pcs : node) (ρs : regbank).
  Implicit Types (Q : value Λt -> value Λs -> rProp).

  Lemma both_ret j i Q vt vs :
    Q vt vs -∗
    [Pt, Ps, C] ([], ReturnState vt) <{j, i}= ([], ReturnState vs) {{ Q }}.
  Proof using Type. by iApply (final). Qed.

  Lemma both_load ct ft pct ρt j i cs fs pcs ρs Q
    I E pct' pcs' dstt dsts srct srcs addrt addrs:
    ft@pct is <<{ dstt := !srct -> pct' }>> ->
    fs@pcs is <<{ dsts := !srcs -> pcs' }>> ->
    ρt @ srct ⇒ addrt ->
    ρs @ srcs ⇒ addrs ->
    same_val I addrt addrs ->
    (∀ ls, addrs = VPtr ls -> ls ∉ sdom E) ->
    (∀ vt vs,
       ⌜same_val I vt vs⌟ -∗
       mem_inj I E -∗
       [Pt, Ps, C] (ct, State ft pct' (⟦dstt ⇐ vt⟧ρt))
            <{1+j, 1+i}=
           (cs, State fs pcs' (⟦dsts ⇐ vs⟧ρs)) {{ Q }}) -∗
    mem_inj I E -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    iIntros (Hpct Hpcs Haddrt Haddrs Hsame Hs) "Hsim Hinj".
    iApply (source_load_exploit with "[Hsim] Hinj"); eauto.
    iIntros (E' lt ls vt vs -> -> ->) "Ht Hs %Hsame' Hinj".
    iApply (target_load with "[-Ht] Ht"); eauto.
    iIntros "Ht".
    iApply "Hsim"; eauto.
    iApply (inj_release_points_to with "Hinj Ht Hs").
    - by set_solver.
    - assert ((ls, lt) ∉ E).
      + intros Hin. eapply Hs.
        * reflexivity.
        * apply sdom_spec. by eexists.
      + by set_solver.
    - done.
  Qed.

  Lemma both_store ct ft pct ρt j i cs fs pcs ρs Q
    I E pct' pcs' dstt dsts srct srcs addrt addrs valt vals:
    ft@pct is <<{ !dstt := srct -> pct' }>> ->
    fs@pcs is <<{ !dsts := srcs -> pcs' }>> ->
    ρt @ dstt ⇒ addrt ->
    ρs @ dsts ⇒ addrs ->
    ρt @ srct ⇒ valt ->
    ρs @ srcs ⇒ vals ->
    same_val I addrt addrs ->
    same_val I valt vals ->
    (∀ ls, addrs = VPtr ls -> ls ∉ sdom E) ->
    (mem_inj I E -∗
       [Pt, Ps, C] (ct, State ft pct' ρt)
            <{1+j, 1+i}=
           (cs, State fs pcs' ρs) {{ Q }}) -∗
    mem_inj I E -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    iIntros (Hpct Hpcs Haddrt Haddrs Hvalt Hvals HsameAddr HsameVal HnE) "Hsim Hinj".
    iApply (source_store_exploit with "[Hsim] Hinj"); eauto.
    iIntros (E' lt ls vt -> -> ->) "Ht Hs Hinj".
    iApply (target_store with "[-Ht] Ht"); eauto.
    iIntros "Ht".
    iApply "Hsim"; eauto.
    iApply (inj_release_points_to with "Hinj Ht Hs").
    - by set_solver.
    - assert ((ls, lt) ∉ E).
      + intros Hin. eapply HnE.
        * reflexivity.
        * apply sdom_spec. by eexists.
      + by set_solver.
    - done.
  Qed.

  Lemma both_alloc ct ft pct ρt j i cs fs pcs ρs Q
    I E pct' pcs' dstt dsts :
    ft@pct is <<{ dstt := alloc () -> pct' }>> ->
    fs@pcs is <<{ dsts := alloc () -> pcs' }>> ->
    (∀ lt ls vt vs,
       ⌜same_val I vt vs⌟ -∗
       lt →ₜ vt -∗
       ls →ₛ vs -∗
       mem_inj I E -∗
       [Pt, Ps, C] (ct, State ft pct' (⟦dstt ⇐ VPtr lt⟧ρt))
                    <{1+j, 1+i}=
                   (cs, State fs pcs' (⟦dsts ⇐ VPtr ls⟧ρs)) {{ Q }}) -∗
    mem_inj I E -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    iIntros (Hpct Hpcs) "Hsim Hinj".
    iApply (source_alloc); eauto.
    iIntros (ls) "Hs".
    iApply (target_alloc); eauto.
    iIntros (lt vt) "Ht".
    iApply ("Hsim" with "[] Ht Hs Hinj").
    iPureIntro. by constructor.
  Qed.

  Lemma both_free ct ft pct ρt j i cs fs pcs ρs Q
    I E pct' pcs' srct srcs addrt addrs :
    ft@pct is <<{ free srct -> pct' }>> ->
    fs@pcs is <<{ free srcs -> pcs' }>> ->
    ρt @ srct ⇒ addrt ->
    ρs @ srcs ⇒ addrs ->
    same_val I addrt addrs ->
    (∀ ls, addrs = VPtr ls -> ls ∉ sdom E) ->
    (mem_inj I E -∗
     [Pt, Ps, C] (ct, State ft pct' ρt)
                  <{1+j, 1+i}=
                 (cs, State fs pcs' ρs) {{ Q }}) -∗
    mem_inj I E -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    iIntros (Hpct Hpcs Hsrct Hsrcs Hrel HnE) "Hsim Hinj".
    iApply (source_free_exploit with "[Hsim] Hinj"); eauto.
    iIntros (? lt ls vt -> -> ->) "Ht Hs Hinj".
    iApply (target_free with "[-Ht] Ht"); eauto.
    iIntros "Ht".
    iApply "Hsim".
    iApply (inj_release_freed with "Hinj Ht Hs").
    - by set_solver.
    - assert ((ls, lt) ∉ E).
      + intros Hin. eapply HnE.
        * reflexivity.
        * apply sdom_spec. by eexists.
      + by set_solver.
  Qed.

  Lemma both_call Pre Post ct ft pct ρt j i cs fs pcs ρs Q
    pct' pcs' dstt dsts fnamet fnames regt regs valt vals fnt fns:
    ft@pct is <<{ dstt := @call fnamet regt -> pct' }>> ->
    fs@pcs is <<{ dsts := @call fnames regs -> pcs' }>> ->
    find_fun Pt fnamet = Some fnt ->
    find_fun Ps fnames = Some fns ->
    ρt @ regt ⇒ valt ->
    ρs @ regs ⇒ vals ->
    [Pt, Ps, C] {{ Pre }} fnt <{j, i}= fns {{ Post }} -∗
    Pre valt vals -∗
    □ (∀ j' i' vt vs,
         ⌜j < j'⌟ -∗
         ⌜i < i'⌟ -∗
         Post vt vs -∗
         [Pt, Ps, C] (ct, State ft pct' (⟦dstt ⇐ vt⟧ρt))
              <{j', i'}=
            (cs, State fs pcs' (⟦dsts ⇐ vs⟧ρs)) {{ Q }}) -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros Hpct Hpcs Hfnt Hfns Hvalt Hvals.
    iIntros "#Hf Hpre Hsim".
    iSpecialize ("Hf" with "Hpre []").
    { iIntros (? ?) "H". by iApply "H". }
    iRevert "Hf Hsim". iStopProof.
    unseal.
    intros ? ? [-> ->] mt ms _ _ Hhoare. smap.
    intros ? ? _ _ [[-> ->] Hsim]. smap.
    eapply chain_source_step with (i' := i). { by econstructor. }
    eapply chain_target_step. { by eexists; econstructor. }
    intros t' Hstept. inv Hstept. simregs. exists j.
    eapply fsim_lfp_rtl_call_bind.
    - exists (S j). simpl. lia.
    - exists (S i). simpl. lia.
    - apply Hhoare.
    - intros j' i' vt vs mt' ms' Hj Hi H.
      replace (mt') with (∅ ∪ ∅ ∪ ∅ ∪ mt') by smap.
      replace (ms') with (∅ ∪ ∅ ∪ ∅ ∪ ms') by smap.
      eapply Hsim.
      + by smap; apply map_disjoint_empty_r.
      + by smap; apply map_disjoint_empty_r.
      + by split.
      + by smap; apply map_disjoint_empty_r.
      + by smap; apply map_disjoint_empty_r.
      + by split.
      + by smap; apply map_disjoint_empty_r.
      + by smap; apply map_disjoint_empty_r.
      + assumption.
  Qed.

  Lemma both_call_framed Pre Post F ct ft pct ρt j i cs fs pcs ρs Q
    pct' pcs' dstt dsts fnamet fnames regt regs valt vals fnt fns:
    ft@pct is <<{ dstt := @call fnamet regt -> pct' }>> ->
    fs@pcs is <<{ dsts := @call fnames regs -> pcs' }>> ->
    find_fun Pt fnamet = Some fnt ->
    find_fun Ps fnames = Some fns ->
    ρt @ regt ⇒ valt ->
    ρs @ regs ⇒ vals ->
    [Pt, Ps, C] {{ Pre }} fnt <{j, i}= fns {{ Post }} -∗
    Pre valt vals -∗
    F -∗
    □ (∀ j' i' vt vs,
         ⌜j < j'⌟ -∗
         ⌜i < i'⌟ -∗
         Post vt vs -∗
         F -∗
         [Pt, Ps, C] (ct, State ft pct' (⟦dstt ⇐ vt⟧ρt))
              <{j', i'}=
            (cs, State fs pcs' (⟦dsts ⇐ vs⟧ρs)) {{ Q }}) -∗
    [Pt, Ps, C] (ct, State ft pct ρt) <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    intros Hpct Hpcs Hfnt Hfns Hvalt Hvals.
    iIntros "Hhoare Hpre HF #Hsim".
    iApply (both_call with "[Hhoare] [Hpre HF]").
    - done.
    - done.
    - done.
    - done.
    - done.
    - done.
    - iApply (frame with "Hhoare").
    - iFrame. iApply "HF".
    - iModIntro. iIntros (j' i' vt vs Hj Hi) "[HPost HP2]".
      iApply ("Hsim" $! j' i' vt vs Hj Hi with "HPost HP2").
  Qed.

End SyncRulesDef.
