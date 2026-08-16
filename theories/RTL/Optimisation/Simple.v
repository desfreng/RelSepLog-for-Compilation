From RSL Require Import Prelude.

From RSL.Logic Require Import Logic.
From RSL.RTL Require Import SimRules.
From RSL.RTL.Optimisation Require Import Commons.

Import RTLNotations.

Definition simple_opt_instr (i: rtl_instr) : rtl_instr :=
  match i with
  | Iop op args dst pc =>
      match op, args with
      | Sub, [src1; src2] =>
          if (src1 =? src2)
          then Iop (ImmInt 0%Z) [] dst pc
          else i
      | Move, [src] =>
          if (src =? dst)
          then Inop pc
          else i
      | _, _ => i
      end
  | Icond b pcT pcF =>
      if (pcT =? pcF)
      then Inop pcT
      else Icond b pcT pcF
  | _ => i
  end.

Definition simple_opt_fun (fn: rtl_function) : rtl_function :=
  {|
    rtl_fn_name := rtl_fn_name fn;
    rtl_fn_regs := rtl_fn_regs fn;
    rtl_fn_entrypoint := rtl_fn_entrypoint fn;
    rtl_fn_code := simple_opt_instr <$> rtl_fn_code fn;
    rtl_fn_regs_no_dup := rtl_fn_regs_no_dup fn;
  |}.

Lemma simple_opt_ni : name_identical simple_opt_fun.
Proof using Type. by intros []. Qed.

Definition simple_opt (p: rtl_program) : rtl_program :=
  {|
    prog_fun_list := simple_opt_fun <$> prog_fun_list p;
    prog_main := prog_main p;
    prog_fun_list_no_dup := opt_no_dup simple_opt_ni (prog_fun_list_no_dup p);
    prog_main_exists := opt_main_some simple_opt_ni (prog_main_exists p)
  |}.

Lemma simple_opt_instr_case op args dst pc :
  (
    op = Move ∧
    args = [dst] ∧
    simple_opt_instr (Iop op args dst pc) = Inop pc
  ) ∨ (
    ∃ src,
      op = Sub ∧
      args = [src; src] ∧
      simple_opt_instr (Iop op args dst pc) = Iop (ImmInt 0%Z) [] dst pc
  ) ∨ (
    simple_opt_instr (Iop op args dst pc) = Iop op args dst pc
  ).
Proof using Type.
  destruct op, args as [|src1 [|src2 []]]; try (by do 2 right).
  - destruct (src1 =? src2) eqn:Heq.
    + right. left. eexists. split_and!; auto.
      * by apply Nat.eqb_eq in Heq as ->.
      * simpl. by rewrite Heq.
    + do 2 right. simpl. by rewrite Heq.
  - destruct (src1 =? dst) eqn:Heq.
    + left. split_and!; auto.
      * by apply Nat.eqb_eq in Heq as ->.
      * simpl. by rewrite Heq.
    + do 2 right. simpl. by rewrite Heq.
Qed.

Lemma simple_opt_find_fun {Ps} fn f:
  find_fun Ps fn = Some f ->
  find_fun (simple_opt Ps) fn = Some (simple_opt_fun f).
Proof using Type. by apply opt_fun_list. Qed.

Section simple_opt.
  Context (Ps : prog rtl_lang).
  Let Pt : prog rtl_lang := simple_opt Ps.

  Definition simple_opt_sim_inv : SInv rtl_lang rtl_lang WfNat WfNat :=
    fun st j i ss ϕ =>
      (∃ I f pc ρt ρs,
          ⌜st = ([], State (simple_opt_fun f) pc ρt)⌟ ∗
          ⌜ss = ([], State f pc ρs)⌟ ∗
          ⌜∀ r, ρt@r <{ I }> ρs@r⌟ ∗
          ⌜∀ vt vs, samer I vt vs ⊢ ϕ vt vs⌟ ∗
          mem_inj I ∅
      )%I.

  Lemma simple_opt_soundness C f I :
    ⊢ [Pt, Ps, C] {{ same_args I }} (simple_opt_fun f) <{0, 0}= f {{ samer I }}.
  Proof using Type.
    iIntros "!>" (valt vals) "[%Harg Hinj]".
    iApply (source_callstate_exploit).
    iIntros (ρs pc Hlen -> ->).
    iApply (target_callstate); auto; first by eapply Forall2_length_r.
    iApply (coind (simple_opt_sim_inv)).
    {
      clear.
      iIntros "!>" (C st j i ss ϕ) "#CIH".
      iIntros "(%I & %f & %pc & %ρt & %ρs & -> & -> & %Hsame & %Hpost & Hinj)".

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

      - iApply (source_nop); first done.
        iApply (target_nop). { simpl. rewrite lookup_fmap Hi. by simpl. }
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, _, _. iFrame. iPureIntro. by split_and!.

      - destruct (multiple_same args Hsame) as (valt & vals & Hvalt & Hvals & Hval).
        iApply (source_op_exploit); try done.
        iIntros (vs Hvs).
        destruct (simple_opt_instr_case op args dst pc') as
          [ (-> & -> & H) | [(? & -> & -> & H) | H]].

        + iApply (target_nop).
          { simpl. rewrite lookup_fmap Hi. eapply fmap_Some.
            eexists. split; [ done | by rewrite H ]. }

          assert (∃ v, vals = [v]) as (v & ->).
          { pose proof (regbank_list_length _ _ _ Hvals) as Hlen.
            destruct vals as [|? [|]]; try inv Hlen. by eexists. }
          inv Hval as [ | ? ? ? ? ? Hforall ]; inv Hforall.
          apply regbank_assert_unfold in Hvals as [Hval _]. inv Hvs.

          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, f, _, _, _. iFrame. iPureIntro.
          split_and!; try done. by apply same_bank_set_useless.

        + iApply (target_op).
          { simpl. rewrite lookup_fmap Hi. eapply fmap_Some.
            eexists. split; [ done | by rewrite H ]. } all: try done.

          assert (∃ v, vals = [v; v]) as (v & ->).
          { pose proof (regbank_list_length _ _ _ Hvals) as Hlen.
            destruct vals as [|? [|? []]]; try inv Hlen.
            apply regbank_assert_unfold in Hvals as [? Hvals].
            apply regbank_assert_unfold in Hvals as [? _]. simregs.
            by eexists. }
          inv Hval as [ | ? ? ? ? ? Hforall ];
            inv Hforall  as [ | ? ? ? ? ? Hforall' ]; inv Hforall'.
          destruct v as [vi | | | ]; inv Hvs.
          rewrite Z.sub_diag.

          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, f, _, _, _. iFrame. iPureIntro.
          split_and!; try done. apply update_same_bank.
          * by constructor.
          * done.

        + destruct (eval_op_same_args Hval Hvs) as (vt & Hvt & Hrel).
          iApply (target_op).
          { simpl. rewrite lookup_fmap Hi. eapply fmap_Some.
            eexists. split; [ done | by rewrite H ]. } all: try done.

          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, f, _, _, _. iFrame. iPureIntro.
          split_and!; try done. by apply update_same_bank.


      - destruct (Hsame src) as (vt & vs & Ht & Hs & Hv).
        iApply (both_load with "[] Hinj").
        { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
        iIntros (vt' vs' Hv') "Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, _, _. iFrame. iPureIntro. split_and!; try done.
        by apply update_same_bank.

      - destruct (Hsame src) as (addrt & addrs & Haddrt & Haddrs & Haddr).
        destruct (Hsame dst) as (dstt & dsts & Hdstt & Hdsts & Hdst).
        iApply (both_store with "[] Hinj").
        { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
        iIntros "Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, _, _. iFrame. iPureIntro. by split_and!.

      - iApply (both_alloc with "[] Hinj").
        { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
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
        + clear -Hpost.
          iPureIntro. iIntros (vt vs) "Hsame".
          iApply Hpost.
          iApply (samer_mono with "Hsame"). by set_solver.

      - destruct (Hsame src) as (addrt & addrs & Haddrt & Haddrs & Haddr).
        iApply (both_free with "[] Hinj").
        { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
        iIntros "Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, _, _. iFrame. iPureIntro. by split_and!.

      - destruct (find_fun Ps fname) as [fn |] eqn:Hfn; last by iApply (source_call_fail).
        destruct (multiple_same args Hsame) as (vals & valt & Hvalt & Hvals & Hval).
        iApply (both_call (same_args I) (samer I) with "[] [Hinj]").
        { simpl. rewrite lookup_fmap Hi. by simpl. } all: eauto.
        + by apply simple_opt_find_fun.
        + clear.
          iIntros "!>" (valt vals) "[%Harg Hinj]".
          iApply (source_callstate_exploit).
          iIntros (ρs pc Hlen -> ->).
          iApply (target_callstate); auto; first by eapply Forall2_length_r.
          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, fn, _, _, _.  iFrame. iPureIntro.
          split_and!; try done. by apply init_same_bank.

        + iFrame. by iPureIntro.

        + iIntros "!>" (j' i' ? ? ? ?) "(%I' & %Hincl & %Hsame' & Hinj)".
          iApply "CIH"; auto.
          iExists I', f, _, _, _. iFrame.
          iSplitR. { by iPureIntro. }
          iSplitR. { by iPureIntro. }
          iSplitR.
          * iPureIntro. apply update_same_bank; first done.
            intros ? ?. by eapply same_bank_mono, Hsame.
          * iPureIntro. iIntros (? ?) "Hsame".
            iApply Hpost. by iApply (samer_mono with "Hsame").

      - destruct (Hsame r) as (bt & bs & Hbt & Hbs & Hb).
        iApply (source_if_exploit); try done.
        iIntros (b pc' -> ->). inv Hb.
        destruct (decide (tpc = fpc)) as [-> | Hneq].
        + iApply (target_nop).
          { simpl. rewrite lookup_fmap Hi. simpl. by rewrite Nat.eqb_refl. }
          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, f, _, _, _.  iFrame. iPureIntro.
          split_and!; try done. by destruct b.
        + apply Nat.eqb_neq in Hneq.
          iApply (target_if).
          { simpl. rewrite lookup_fmap Hi. simpl. by rewrite Hneq. }
          all: try done.
          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, f, _, _, _.  iFrame. iPureIntro.
          by split_and!.

      - destruct (Hsame r) as (vt & vs & Hvt & Hvs & Hr).
        iApply (source_ret); try done.
        iApply (target_ret).
        { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
        iApply (both_ret). iApply Hpost.
        iExists I. iFrame. by iPureIntro.

      - by iApply (source_fail).

    }
    iExists _, _, _, _, _. iFrame. iPureIntro.
    split_and!; try done. by apply init_same_bank.
  Qed.
End simple_opt.
