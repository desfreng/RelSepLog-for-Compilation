From RSL Require Import Prelude.

From RSL.Logic Require Import Logic.
From RSL.RTL Require Import SimRules.

Import RTLNotations.

Definition no_opt_fun (fs: rtl_function) : rtl_function :=
  {|
    rtl_fn_name := rtl_fn_name fs;
    rtl_fn_regs := rtl_fn_regs fs;
    rtl_fn_entrypoint := rtl_fn_entrypoint fs;
    rtl_fn_code := rtl_fn_code fs;
    rtl_fn_regs_no_dup := rtl_fn_regs_no_dup fs
  |}.

Lemma no_opt_no_dup {Ps}:
  is_no_dup (rtl_fn_name <$> prog_fun_list Ps) = true ->
  is_no_dup (rtl_fn_name <$> fmap no_opt_fun (prog_fun_list Ps)) = true.
Proof using Type.
  rewrite !is_no_dup_sound.
  induction (prog_fun_list Ps) as [ | f l IH ].
  - done.
  - simpl. intros H. inv H as [| ? ? HnIn HnDup].
    constructor; auto.
    intros (? & Heq & (f' & -> & H)%list_elem_of_fmap)%list_elem_of_fmap.
    apply HnIn. rewrite Heq.
    apply list_elem_of_fmap.
    by exists f'.
Qed.

Lemma no_opt_find_fun_list {Ps} fn f:
  find_fun_in_list (prog_fun_list Ps) fn = Some f ->
  find_fun_in_list (no_opt_fun <$> prog_fun_list Ps) fn = Some (no_opt_fun f).
Proof using Type.
  unfold find_fun_in_list.
  intros ([? f'] & H & Heq)%fmap_Some. simpl in Heq. subst f'.
  apply list_find_Some in H as (Hres & Hp & Hfirst).
  rewrite fmap_Some. eexists (_, _). split; last reflexivity.
  apply list_find_Some. split_and!.
  - apply list_lookup_fmap_Some. by eexists.
  - done.
  - intros j ? (f' & -> & Hin)%list_lookup_fmap_Some Hj. simpl.
    by eapply Hfirst.
Qed.

Lemma no_opt_main_some {Ps}:
  is_Some (find_fun_in_list (prog_fun_list Ps) (prog_main Ps)) ->
  is_Some (find_fun_in_list (no_opt_fun <$> prog_fun_list Ps) (prog_main Ps)).
Proof using Type. intros [f H]. eexists. by apply no_opt_find_fun_list. Qed.

Definition no_opt (Ps: rtl_program) : rtl_program :=
  {|
    prog_fun_list := fmap no_opt_fun (prog_fun_list Ps);
    prog_main := prog_main Ps;
    prog_fun_list_no_dup := no_opt_no_dup (prog_fun_list_no_dup Ps);
    prog_main_exists := no_opt_main_some (prog_main_exists Ps)
  |}.

Lemma no_opt_find_fun {Ps} fn f:
  find_fun Ps fn = Some f ->
  find_fun (no_opt Ps) fn = Some (no_opt_fun f).
Proof using Type. by apply no_opt_find_fun_list. Qed.

Section no_opt.
  Context (Ps : rtl_program).
  Let Pt := no_opt Ps.

  Definition no_opt_sim_inv : SInv rtl_lang rtl_lang WfNat WfNat :=
    fun st j i ss ϕ =>
      (∃ I f pc ρt ρs,
          ⌜st = ([], State (no_opt_fun f) pc ρt)⌟ ∗
          ⌜ss = ([], State f pc ρs)⌟ ∗
          ⌜∀ r, ρt@r <{ I }> ρs@r⌟ ∗
          mem_inj I ∅ ∗
          (∀ vt vs, samer I vt vs -∗ ϕ vt vs)
      )%I.

  Lemma no_opt_soundness C f I :
    ⊢ [Pt, Ps, C] {{ same_args I }} (no_opt_fun f) <{0, 0}= f {{ samer I }}.
  Proof using Type.
    iIntros "!>" (valt vals Ψ) "[%Harg Hinj] Hpost".
    iApply (source_callstate_exploit).
    iIntros (ρs pc Hlen -> ->).
    iApply (target_callstate); auto; first by eapply Forall2_length_r.
    simpl.
    iApply (coind no_opt_sim_inv).
    {
      clear.
      iIntros "!>" (C st j i ss ϕ) "#CIH".
      iIntros "(%I & %f & %pc & %ρt & %ρs & -> & -> & %Hsame & Hinj & Hpost)".
      destruct ((rtl_fn_code f) !! pc)
        as [
          [ pc'
          | op args dst pc'
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
        iApply (target_nop); try done.
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, ρt, ρs. iFrame. iPureIntro. by split_and!.

      - destruct (multiple_same args Hsame) as (vals & valt & Hvalt & Hvals & Hval).
        iApply (source_op_exploit); try done.
        iIntros (vs Hvs).
        destruct (eval_op_same_args Hval Hvs) as (vt & Hvt & Hrel).
        iApply (target_op); try done.
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, _, _. iFrame. iPureIntro. split_and!; try done.
        by apply update_same_bank.

      - destruct (Hsame src) as (vt & vs & Ht & Hs & Hv).
        iApply (both_load with "[Hpost] Hinj"); try done.
        iIntros (vt' vs' Hv') "Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, _, _. iFrame. iPureIntro. split_and!; try done.
        by apply update_same_bank.

      - destruct (Hsame src) as (addrt & addrs & Haddrt & Haddrs & Haddr).
        destruct (Hsame dst) as (dstt & dsts & Hdstt & Hdsts & Hdst).
        iApply (both_store with "[Hpost] Hinj"); try done.
        iIntros "Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, _, _. iFrame. iPureIntro. by split_and!.

      - iApply (both_alloc with "[Hpost] Hinj"); try done.
        iIntros (lt ls vt vs Hrel) "Ht Hs Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iPoseProof (inj_insert_points_to with "Hinj Ht Hs [//]") as "H"; eauto.
        iExists _, f, _, _, _. iFrame.
        iSplitR. { by iPureIntro. }
        iSplitR. { by iPureIntro. }
        iSplitR.
        + iPureIntro. apply update_same_bank.
          * constructor. unfold related. by set_solver.
          * intros ? _. eapply same_bank_mono; last done. by set_solver.
        + clear.
          iIntros (vt vs) "Hsame".
          iApply "Hpost".
          iApply (samer_mono with "Hsame"). by set_solver.

      - destruct (Hsame src) as (addrt & addrs & Haddrt & Haddrs & Haddr).
        iApply (both_free with "[Hpost] Hinj"); try done.
        iIntros "Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, _, _. iFrame. iPureIntro. by split_and!.

      - destruct (find_fun Ps fname) as [fn |] eqn:Hfn; last by iApply (source_call_fail).
        destruct (multiple_same args Hsame) as (vals & valt & Hvalt & Hvals & Hval).
        iApply (both_call_framed (same_args I) (samer I) with "[] [Hinj] Hpost"); eauto.
        + by apply no_opt_find_fun.
        + clear.
          iIntros "!>" (valt vals Ψ) "[%Harg Hinj] Hpost".
          iApply (source_callstate_exploit).
          iIntros (ρs pc Hlen -> ->).
          iApply (target_callstate); auto; first by eapply Forall2_length_r.
          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, fn, _, _, _.  iFrame. iPureIntro.
          split_and!.
          * done.
          * done.
          * by apply init_same_bank.
        + iFrame. by iPureIntro.
        + iIntros "!>" (j' i' ? ? ? ?) "(%I' & %Hincl & %Hsame' & Hinj) Hpost".
          iApply "CIH"; auto.
          iExists I', f, _, _, _. iFrame.
          iSplitR. { by iPureIntro. }
          iSplitR. { by iPureIntro. }
          iSplitR.
          * iPureIntro. apply update_same_bank; first done.
            intros ? ?. by eapply same_bank_mono, Hsame.
          * iIntros (? ?) "Hsame". iApply "Hpost". by iApply (samer_mono with "Hsame").

      - destruct (Hsame r) as (bt & bs & Hbt & Hbs & Hb).
        iApply (source_if_exploit); try done.
        iIntros (b pc' -> ->). inv Hb.
        iApply (target_if); try done.
        iApply "CIH"; simpl; try (iPureIntro; lia).
        iExists I, _, _, _, _.  iFrame. iPureIntro. by split_and!.

      - destruct (Hsame r) as (vt & vs & Hvt & Hvs & Hr).
        iApply (source_ret); try done.
        iApply (target_ret); try done.
        iApply (both_ret). iApply "Hpost".
        iExists I. iFrame. by iPureIntro.

      - by iApply (source_fail).
    }
    iExists I, f, _, _, _. iFrame.
    iPureIntro. split_and!.
    - reflexivity.
    - reflexivity.
    - by apply init_same_bank.
  Qed.
End no_opt.
