From RSL Require Import Prelude.

From RSL.Logic Require Import Logic.
From RSL.RTL Require Import SimRules.

Section identity.
  Context (Pt Ps : prog rtl_lang).

  Definition fun_equivalent (f1 f2: rtl_function) :=
    rtl_fn_name f1 = rtl_fn_name f2 ∧
    rtl_fn_regs f1 = rtl_fn_regs f2 ∧
    rtl_fn_entrypoint f1 = rtl_fn_entrypoint f2 ∧
    rtl_fn_code f1 = rtl_fn_code f2.

  Lemma pc_eq ft fs pc i:
    fun_equivalent ft fs ->
    fs @ pc is i ->
    ft @ pc is i.
  Proof using Type. by intros (_ & _ & _ & ->) Hpc. Qed.

  Hypothesis fun_incl:
    ∀ fn fs,
    find_fun Ps fn = Some fs ->
    ∃ ft, find_fun Pt fn = Some ft ∧ fun_equivalent ft fs.

  Definition id_sim_inv : SInv rtl_lang rtl_lang WfNat WfNat :=
    fun st j i ss ϕ =>
      (∃ I ft fs pc ρt ρs,
          ⌜st = ([], State ft pc ρt)⌟ ∗
          ⌜ss = ([], State fs pc ρs)⌟ ∗
          ⌜fun_equivalent ft fs⌟ ∗
          ⌜∀ r, ρt@r <{ I }> ρs@r⌟ ∗
          ⌜∀ vt vs, samer I vt vs ⊢ ϕ vt vs⌟ ∗
          mem_inj I ∅
      )%I.

  Lemma sim_refl (j i: nat) C ft fs pc ρt ρs I :
    fun_equivalent ft fs ->
    (∀ r, ρt @ r <{ I }> ρs @ r) ->
    mem_inj I ∅ -∗
    [Pt, Ps, C] ([], State ft pc ρt) <{ j, i }= ([], State fs pc ρs) {{ samer I }}.
  Proof using fun_incl.
    iIntros (Heq Hsame) "Hinj".
    iApply (coind id_sim_inv).
    {
      clear -fun_incl.
      iIntros "!>" (C st j i ss ϕ) "#CIH".
      iIntros "(%I & %ft & %fs & %pc & %ρt & %ρs & H)".
      iDestruct "H" as "(-> & -> & %Hfeq & %Hsame & %Hpost & Hinj)".
      destruct ((rtl_fn_code fs) !! pc)
        as [
          [ pc'
          | op args dst pc'
          | dst pc'
          | src dst pc'
          | dst src pc'
          | dst pc'
          | src pc'
          | fname args dst pc'
          | r tpc fpc
          | r
          ]
        |] eqn:Hi.
      - iApply (source_nop); try done.
        iApply (target_nop); [ by eapply pc_eq | ].
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, ft, fs, _, ρt, ρs. iFrame. iPureIntro. by split_and!.

      - destruct (multiple_same args Hsame) as (vals & valt & Hvalt & Hvals & Hval).
        iApply (source_op_exploit); try done.
        iIntros (vs Hvs).
        destruct (eval_op_same_args Hval Hvs) as (vt & Hvt & Hrel).
        iApply (source_op); try done.
        iApply (target_op); [ by eapply pc_eq | done | done | ].
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, ft, fs, _, _, _. iFrame. iPureIntro. split_and!; try done.
        apply update_same_bank.
        + done.
        + intros ? ?. apply Hsame.

      - iApply (target_random); [ by eapply pc_eq | ].
        iIntros (v).
        iApply (source_random); try done.
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, ft, fs, _, _, _. iFrame. iPureIntro. split_and!; try done.
        apply update_same_bank.
        + by constructor.
        + intros ? ?. apply Hsame.

      - destruct (Hsame src) as (vt & vs & Ht & Hs & Hv).
        iApply (both_load with "[] Hinj");
          [ by eapply pc_eq | done | done | done | done | done | ].
        iIntros (vt' vs' Hv') "Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, ft, fs, _, _, _. iFrame. iPureIntro. split_and!; try done.
        apply update_same_bank.
        + done.
        + intros ? ?. apply Hsame.

      - destruct (Hsame src) as (addrt & addrs & Haddrt & Haddrs & Haddr).
        destruct (Hsame dst) as (dstt & dsts & Hdstt & Hdsts & Hdst).
        iApply (both_store with "[] Hinj");
          [ by eapply pc_eq | done | done | done | done | done | done | done | done | ].
        iIntros "Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, ft, fs, _, _, _. iFrame. iPureIntro. by split_and!.

      - iApply (both_alloc with "[] Hinj");
          [ by eapply pc_eq | done | ].
        iIntros (lt ls vt vs Hrel) "Ht Hs Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iPoseProof (inj_insert_points_to with "Hinj Ht Hs [//]") as "H"; eauto.
        iExists _, ft, fs, _, _, _. iFrame.
        iSplitR. { by iPureIntro. }
        iSplitR. { by iPureIntro. }
        iSplitR. { by iPureIntro. }
        iSplitR.
        + iPureIntro. apply update_same_bank.
          * constructor. unfold related. by set_solver.
          * intros ? _. eapply same_bank_mono; last done. by set_solver.
        + clear -Hpost.
          iPureIntro. iIntros (vt vs) "Hsame".
          iApply (Hpost). iApply (samer_mono with "Hsame"). by set_solver.

      - destruct (Hsame src) as (addrt & addrs & Haddrt & Haddrs & Haddr).
        iApply (both_free with "[] Hinj");
          [ by eapply pc_eq | done | done | done | done | done | ].
        iIntros "Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, ft, fs, _, _, _. iFrame. iPureIntro. by split_and!.

      - destruct (find_fun Ps fname) as [fns|] eqn:Hfns; last by iApply (source_call_fail).
        destruct (multiple_same args Hsame) as (vals & valt & Hvalt & Hvals & Hval).
        destruct (fun_incl _ _ Hfns) as (fnt & Hfnt & Heq).
        iApply (both_call (same_args I) (samer I) with "[] [Hinj]");
          [ by eapply pc_eq | done | done | done | done | done | | | ].
        + clear -Heq.
          iIntros "!>" (valt vals) "[%Harg Hinj]".
          iApply (source_callstate_exploit).
          iIntros (Hlen).
          iApply (source_callstate); try done.
          iApply (target_callstate); try done.
          { destruct Heq as (_ & -> & _ & _). by eapply Forall2_length_r. }
          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, fnt, fns, _, _, _.  iFrame. iPureIntro.
          split_and!.
          * done.
          * by destruct Heq as (_ & _ & -> & _).
          * done.
          * by destruct Heq as (_ & -> & _ & _); apply init_same_bank.
          * by iIntros (? ? ) "$".
        + iFrame. by iPureIntro.
        + iIntros (j' i' ? ? ? ?) "(%I' & %Hincl & %Hsame' & Hinj)".
          iApply "CIH"; auto.
          iExists I', ft, fs, _, _, _. iFrame.
          iSplitR. { by iPureIntro. }
          iSplitR. { by iPureIntro. }
          iSplitR. { by iPureIntro. }
          iSplitR.
          * iPureIntro. apply update_same_bank; first done.
            intros ? ?. by eapply same_bank_mono, Hsame.
          * iPureIntro. iIntros (? ?) "Hsame".
            iApply Hpost. by iApply (samer_mono with "Hsame").

      - destruct (Hsame r) as (bt & bs & Hbt & Hbs & Hb).
        iApply (source_if_exploit); try done.
        iIntros (b ->). inv Hb.
        iApply (source_if); try done.
        iApply (target_if); [ by eapply pc_eq | done | ].
        iApply "CIH"; simpl; try (iPureIntro; lia).
        iExists I, ft, fs, _, _, _.  iFrame. iPureIntro. by split_and!.

      - destruct (Hsame r) as (vt & vs & Hvt & Hvs & Hr).
        iApply (source_ret); try done.
        iApply (target_ret); [ by eapply pc_eq | done | ].
        iApply (both_ret). iApply Hpost.
        iExists I. iFrame. by iPureIntro.

      - by iApply (source_fail).
    }
    iExists I, ft, fs, _, _, _. iFrame.
    iPureIntro. split_and!.
    - reflexivity.
    - reflexivity.
    - done.
    - done.
    - by iIntros (? ?) "$".
  Qed.

  Lemma hoare_refl (j i: nat) C ft fs I :
    fun_equivalent ft fs ->
    ⊢ [Pt, Ps, C] {{ same_args I }} ft <{j, i}= fs {{ samer I }}.
  Proof using fun_incl.
    intros Heq.
    iIntros "!>" (valt vals) "[%Harg Hinj]".
    iApply (source_callstate_exploit).
    iIntros (Hlen).
    iApply (source_callstate); try done.
    iApply (target_callstate); try done.
    { destruct Heq as (_ & -> & _ & _). by eapply Forall2_length_r. }
    destruct Heq as (Hname & Hentry & Hregs & Hcode).
    rewrite Hregs Hentry.
    iApply (sim_refl with "Hinj").
    - done.
    - by apply init_same_bank.
  Qed.
End identity.
