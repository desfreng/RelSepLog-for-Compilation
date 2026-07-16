From RSL Require Import Prelude.

From RSL.RTL Require Export TargetRules SourceRules.

Import RTLNotations.

Section SyncRulesDef.
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

  Lemma both_final C vt j i vs Q :
    Q vt vs -∗
    [C] ([], ReturnState vt) <{j, i}= ([], ReturnState vs) {{ Q }}.
  Proof using Type.
    unseal.
    intros ? ? [-> ->] mt ms _ _ HQ.
    rewrite !map_empty_union.

    eapply FRelated.
    by eexists _, _.
  Qed.

  Lemma both_load I C ct ft pct ρt j i cs fs pcs ρs Q :
    ∀ pct' pcs' dstt dsts srct srcs addrt addrs,
    ft@pct is <<{ dstt := !srct -> pct' }>> ->
    fs@pcs is <<{ dsts := !srcs -> pcs' }>> ->
    ρt @ srct ⇒ addrt ->
    ρs @ srcs ⇒ addrs ->
    same_val I addrt addrs ->
    (∀ vt vs,
       ⌜same_val I vt vs⌟ -∗
       mem_inj I ∅ -∗
       [C] (ct, State ft pct' (⟦dstt ⇐ vt⟧ρt))
            <{1+j, 1+i}=
           (cs, State fs pcs' (⟦dsts ⇐ vs⟧ρs)) {{ Q }}) -∗
    mem_inj I ∅ -∗
    [C] (ct, State ft pct ρt) <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    iIntros (pct' pcs' dstt dsts srct srcs addrt addrs).
    iIntros (Hpct Hpcs Haddrt Haddrs Hsame) "Hsim Hinj".
    iApply (source_load_exploit with "[Hsim] Hinj"); eauto.
    iIntros (lt ls vt vs -> ->) "Ht Hs %Hsame' Hinj".
    iApply (target_load with "[-Ht] Ht"); eauto.
    iIntros "Ht".
    iApply "Hsim"; eauto.
    replace (∅) with (delete ls (<[ls:=lt]> ∅) : gmap loc loc) at 2.
    - iApply (inj_release with "Hinj Ht Hs").
      + by rewrite lookup_insert_eq.
      + done.
    - rewrite delete_insert_eq.
      by rewrite delete_empty.
  Qed.

  Lemma both_store I C ct ft pct ρt j i cs fs pcs ρs Q :
    ∀ pct' pcs' dstt dsts srct srcs addrt addrs valt vals,
    ft@pct is <<{ !dstt := srct -> pct' }>> ->
    fs@pcs is <<{ !dsts := srcs -> pcs' }>> ->
    ρt @ dstt ⇒ addrt ->
    ρs @ dsts ⇒ addrs ->
    ρt @ srct ⇒ valt ->
    ρs @ srcs ⇒ vals ->
    same_val I addrt addrs ->
    same_val I valt vals ->
    (mem_inj I ∅ -∗
       [C] (ct, State ft pct' ρt)
            <{1+j, 1+i}=
           (cs, State fs pcs' ρs) {{ Q }}) -∗
    mem_inj I ∅ -∗
    [C] (ct, State ft pct ρt) <{j, i}= (cs, State fs pcs ρs) {{ Q }}.
  Proof using Type.
    iIntros (pct' pcs' dstt dsts srct srcs addrt addrs valt vals).
    iIntros (Hpct Hpcs Haddrt Haddrs Hvalt Hvals HsameAddr HsameVal) "Hsim Hinj".
    iApply (source_store_exploit with "[Hsim] Hinj"); eauto.
    iIntros (lt ls vt -> ->) "Ht Hs Hinj".
    iApply (target_store with "[-Ht] Ht"); eauto.
    iIntros "Ht".
    iApply "Hsim"; eauto.
    replace (∅) with (delete ls (<[ls:=lt]> ∅) : gmap loc loc) at 2.
    - iApply (inj_release with "Hinj Ht Hs").
      + by rewrite lookup_insert_eq.
      + done.
    - rewrite delete_insert_eq.
      by rewrite delete_empty.
  Qed.
End SyncRulesDef.
