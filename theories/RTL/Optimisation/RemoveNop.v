From RSL Require Import Prelude.

From RSL.Logic Require Import Logic.
From RSL.RTL Require Import SimRules.
From RSL.RTL.Optimisation Require Import Commons.

Import RTLNotations.

Definition is_nop (c : rtl_code) (pc: node) : option node :=
  match c !! pc with
  | Some (Inop next) => Some next
  | _ => None
  end.

Fixpoint find_next_pc (fuel: nat) (c: rtl_code) (n: node) : node :=
  match fuel with
  | 0 => n
  | S f =>
      match is_nop c n with
      | Some next => find_next_pc f c next
      | None => n
      end
  end.

Definition redirect_instr (f: node -> node) (i: rtl_instr) : rtl_instr :=
  match i with
  | Inop succ => Inop (f succ)
  | Iop op args dst succ => Iop op args dst (f succ)
  | Irand dst succ => Irand dst (f succ)
  | Iload addr dst succ => Iload addr dst (f succ)
  | Istore addr src succ => Istore addr src (f succ)
  | Ialloc dst succ => Ialloc dst (f succ)
  | Ifree addr succ => Ifree addr (f succ)
  | Icall sig args dst succ => Icall sig args dst (f succ)
  | Icond cond ifso ifnot => Icond cond (f ifso) (f ifnot)
  | Ireturn reg => Ireturn reg
  end.

Definition remove_nop_fun (depth: nat) (fn: rtl_function) : rtl_function :=
  let c := rtl_fn_code fn in
  let new_c := redirect_instr (find_next_pc depth c) <$> c in
  let new_entry := find_next_pc depth c $ rtl_fn_entrypoint fn in
  {|
    rtl_fn_name := rtl_fn_name fn;
    rtl_fn_regs := rtl_fn_regs fn;
    rtl_fn_entrypoint := new_entry;
    rtl_fn_code := new_c;
    rtl_fn_regs_no_dup := rtl_fn_regs_no_dup fn;
  |}.

Lemma remove_nop_ni {d} : name_identical (remove_nop_fun d).
Proof using Type. by intros []. Qed.

Lemma is_nop_Some f pc pc':
  is_nop (rtl_fn_code f) pc = Some pc' ->
  f @ pc is <<{ nop -> pc' }>>.
Proof using Type.
  unfold is_nop. intros H. repeat case_match; congruence.
Qed.

Lemma find_next_pc_O c n : find_next_pc 0 c n = n.
Proof. done. Qed.

Lemma find_next_pc_no_nop c n d :
  is_nop c n = None -> find_next_pc d c n = n.
Proof. destruct d; simpl; auto. by intros ->. Qed.

Lemma find_next_pc_nop c n n' d' :
  is_nop c n = Some n' -> find_next_pc (S d') c n = find_next_pc d' c n'.
Proof. intros H. simpl. by rewrite H. Qed.

Definition remove_nop (depth: nat) (p: rtl_program) : rtl_program :=
  {|
    prog_fun_list := remove_nop_fun depth <$> prog_fun_list p;
    prog_main := prog_main p;
    prog_fun_list_no_dup := opt_no_dup remove_nop_ni (prog_fun_list_no_dup p);
    prog_main_exists := opt_main_some remove_nop_ni (prog_main_exists p)
  |}.

Lemma remove_nop_find_fun {Ps} d fn f:
  find_fun Ps fn = Some f ->
  find_fun (remove_nop d Ps) fn = Some (remove_nop_fun d f).
Proof using Type. by apply opt_fun_list. Qed.

Section remove_nop.
  Context (Ps : prog rtl_lang) (depth : nat).
  Let Pt : prog rtl_lang := remove_nop depth Ps.

  Definition remove_nop_sim_inv : SInv rtl_lang rtl_lang WfNat WfNat :=
    fun st j i ss ϕ =>
      (∃ I f d pct pcs ρt ρs,
          ⌜st = ([], State (remove_nop_fun depth f) pct ρt)⌟ ∗
          ⌜ss = ([], State f pcs ρs)⌟ ∗
          ⌜pct = find_next_pc d (rtl_fn_code f) pcs⌟ ∗
          ⌜∀ r, ρt@r <{ I }> ρs@r⌟ ∗
          ⌜∀ vt vs, samer I vt vs ⊢ ϕ vt vs⌟ ∗
          mem_inj I ∅
      )%I.

  Lemma remove_nop_soundness C f I :
    ⊢ [Pt, Ps, C] {{ same_args I }} (remove_nop_fun depth f) <{0, 0}= f {{ samer I }}.
  Proof using Type.
    iIntros "!>" (valt vals) "[%Harg Hinj]".
    iApply (source_callstate_exploit).
    iIntros (Hlen).
    iApply (source_callstate); auto.
    iApply (target_callstate); auto; first by eapply Forall2_length_r.
    iApply (coind (remove_nop_sim_inv)).
    {
      clear.
      iIntros "!>" (C st j i ss ϕ) "#CIH".
      iIntros "(%I & %f & %d & %pct & %pcs & %ρt & %ρs & -> & -> & -> & %Hsame & %Hpost & Hinj)".
      iInduction d as [ | d IH ] "IHd" forall (pcs ρt ρs Hsame).
      {
        rewrite find_next_pc_O.
        destruct ((rtl_fn_code f) !! pcs)
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

        - iApply (source_nop); first done.
          iApply (target_nop). { simpl. rewrite lookup_fmap Hi. by simpl. }
          iApply "CIH"; try (iPureIntro; simpl; lia).
          iExists I, f, depth, _, _, _, _. iFrame. iPureIntro. by split_and!.

        - destruct (multiple_same args Hsame) as (vals & valt & Hvalt & Hvals & Hval).
          iApply (source_op_exploit); try done.
          iIntros (vs Hvs).
          iApply (source_op); try done.
          destruct (eval_op_same_args Hval Hvs) as (vt & Hvt & Hrel).
          iApply (target_op).
          { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, f, _, _, _, _, _. iFrame. iPureIntro.
          split_and!; try done. by apply update_same_bank.

        - iApply (target_random).
          { simpl. rewrite lookup_fmap Hi. by simpl. }
          iIntros (v).
          iApply (source_random); try done.
          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, f, _, _, _, _, _. iFrame. iPureIntro.
          split_and!; try done. apply update_same_bank.
          + by constructor.
          + done.

        - destruct (Hsame src) as (vt & vs & Ht & Hs & Hv).
          iApply (both_load with "[] Hinj").
          { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
          iIntros (vt' vs' Hv') "Hinj".
          iApply "CIH"; try (iPureIntro; simpl; lia).
          iExists I, f, _, _, _, _, _. iFrame. iPureIntro. split_and!; try done.
          by apply update_same_bank.

        - destruct (Hsame src) as (addrt & addrs & Haddrt & Haddrs & Haddr).
          destruct (Hsame dst) as (dstt & dsts & Hdstt & Hdsts & Hdst).
          iApply (both_store with "[] Hinj").
          { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
          iIntros "Hinj".
          iApply "CIH"; try (iPureIntro; simpl; lia).
          iExists I, f, _, _, _, _, _. iFrame. iPureIntro. by split_and!.

        - iApply (both_alloc with "[] Hinj").
          { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
          iIntros (lt ls vt vs Hrel) "Ht Hs Hinj".
          iApply "CIH"; try (iPureIntro; simpl; lia).
          iPoseProof (inj_insert_points_to with "Hinj Ht Hs [//]") as "H"; eauto.
          iExists _, f, _, _, _, _, _. iFrame.
          iSplitR. { by iPureIntro. }
          iSplitR. { by iPureIntro. }
          iSplitR. { by iPureIntro. }
          iSplitR.
          + iPureIntro. apply update_same_bank.
            * constructor. unfold related. by set_solver.
            * intros ? _. eapply same_bank_mono; last done. by set_solver.
          + clear -Hpost. iPureIntro.
            iIntros (vt vs) "Hsame".
            iApply (Hpost).
            iApply (samer_mono with "Hsame"). by set_solver.

        - destruct (Hsame src) as (addrt & addrs & Haddrt & Haddrs & Haddr).
          iApply (both_free with "[] Hinj").
          { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
          iIntros "Hinj".
          iApply "CIH"; try (iPureIntro; simpl; lia).
          iExists I, f, _, _, _, _, _. iFrame. iPureIntro. by split_and!.

        - destruct (find_fun Ps fname) as [fn |] eqn:Hfn; last by iApply (source_call_fail).
          destruct (multiple_same args Hsame) as (vals & valt & Hvalt & Hvals & Hval).
          iApply (both_call (same_args I) (samer I) with "[] [Hinj]").
          { simpl. rewrite lookup_fmap Hi. by simpl. } all: eauto.
          + by apply remove_nop_find_fun.
          + clear.
            iIntros "!>" (valt vals) "[%Harg Hinj]".
            iApply (source_callstate_exploit).
            iIntros (Hlen).
            iApply (source_callstate); auto.
            iApply (target_callstate); auto; first by eapply Forall2_length_r.
            iApply "CIH"; simpl; try (iPureIntro; lia).
            iExists I, fn, _, _, _, _, _.  iFrame. iPureIntro.
            split_and!; try done. by apply init_same_bank.

          + iFrame. iPureIntro. exact Hval.

          + iIntros (j' i' ? ? ? ?) "(%I' & %Hincl & %Hsame' & Hinj)".
            iApply "CIH"; auto.
            iExists I', f, _, _, _, _, _. iFrame.
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
          iApply (target_if).
          { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, f, _, _, _, _, _.  iFrame. iPureIntro.
          split_and!; try done. by destruct b.

        - destruct (Hsame r) as (vt & vs & Hvt & Hvs & Hr).
          iApply (source_ret); try done.
          iApply (target_ret).
          { simpl. rewrite lookup_fmap Hi. by simpl. } all: try done.
          iApply (both_ret). iApply Hpost.
          iExists I. iFrame. by iPureIntro.

        - by iApply (source_fail).

      }
      {

        destruct (is_nop (rtl_fn_code f) pcs) as [pc' | ] eqn:Hnop.
        {
          erewrite find_next_pc_nop; eauto.
          iApply (source_nop_noinc); first by apply is_nop_Some.
          iApply ("IHd" with "[] Hinj").
          by iPureIntro.
        }

        erewrite find_next_pc_no_nop; eauto.
        iClear "IHd".
        destruct ((rtl_fn_code f) !! pcs)
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
          |] eqn:Hs;
          try (eassert (Ht: remove_nop_fun depth f @ pcs is _);
               [simpl; rewrite lookup_fmap Hs; by simpl|]).

        - iApply (source_nop); first done.
          iApply (target_nop); first done.
          iApply "CIH"; try (iPureIntro; simpl; lia).
          iExists I, f, depth, _, _, _, _. iFrame. iPureIntro. by split_and!.

        - destruct (multiple_same args Hsame) as (vals & valt & Hvalt & Hvals & Hval).
          iApply (source_op_exploit); try done.
          iIntros (vs Hvs).
          iApply (source_op); try done.
          destruct (eval_op_same_args Hval Hvs) as (vt & Hvt & Hrel).
          iApply (target_op); try done.
          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, f, _, _, _, _, _. iFrame. iPureIntro.
          split_and!; try done. by apply update_same_bank.

        - iApply (target_random); try done.
          iIntros (v).
          iApply (source_random); try done.
          iApply "CIH"; simpl; try (iPureIntro; lia).
          iExists I, f, _, _, _, _, _. iFrame. iPureIntro.
          split_and!; try done. apply update_same_bank.
          + by constructor.
          + done.

        - destruct (Hsame src) as (vt & vs & Hvt & Hvs & Hv).
          iApply (both_load with "[] Hinj"); try done.
          iIntros (vt' vs' Hv') "Hinj".
          iApply "CIH"; try (iPureIntro; simpl; lia).
          iExists I, f, _, _, _, _, _. iFrame. iPureIntro. split_and!; try done.
          by apply update_same_bank.

        - destruct (Hsame src) as (addrt & addrs & Haddrt & Haddrs & Haddr).
          destruct (Hsame dst) as (dstt & dsts & Hdstt & Hdsts & Hdst).
          iApply (both_store with "[] Hinj"); try done.
          iIntros "Hinj".
          iApply "CIH"; try (iPureIntro; simpl; lia).
          iExists I, f, _, _, _, _, _. iFrame. iPureIntro. by split_and!.

        - iApply (both_alloc with "[] Hinj"); try done.
          iIntros (lt ls vt vs Hrel) "Ht Hs Hinj".
          iApply "CIH"; try (iPureIntro; simpl; lia).
          iPoseProof (inj_insert_points_to with "Hinj Ht Hs [//]") as "H"; eauto.
          iExists _, f, _, _, _, _, _. iFrame.
          iSplitR. { by iPureIntro. }
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
          iApply (both_free with "[] Hinj"); try done.
          iIntros "Hinj".
          iApply "CIH"; try (iPureIntro; simpl; lia).
          iExists I, f, _, _, _, _, _. iFrame. iPureIntro. by split_and!.

        - destruct (find_fun Ps fname) as [fn |] eqn:Hfn; last by iApply (source_call_fail).
          destruct (multiple_same args Hsame) as (vals & valt & Hvalt & Hvals & Hval).
          iApply (both_call (same_args I) (samer I) with "[] [Hinj]");
            try done.
          + by apply remove_nop_find_fun.
          + clear.
            iIntros "!>" (valt vals) "[%Harg Hinj]".
            iApply (source_callstate_exploit).
            iIntros (Hlen).
            iApply (source_callstate); auto.
            iApply (target_callstate); auto; first by eapply Forall2_length_r.
            iApply "CIH"; simpl; try (iPureIntro; lia).
            iExists I, fn, _, _, _, _, _.  iFrame. iPureIntro.
            split_and!; try done. by apply init_same_bank.

          + iFrame. iPureIntro. done.

          + iIntros (j' i' ? ? ? ?) "(%I' & %Hincl & %Hsame' & Hinj)".
            iApply "CIH"; auto.
            iExists I', f, _, _, _, _, _. iFrame.
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
          iApply (target_if); try done.
          iApply "CIH"; try (iPureIntro; simpl; lia).
          iExists I, f, _, _, _, _, _. iFrame. iPureIntro.
          split_and!; try done. by destruct b.

        - destruct (Hsame r) as (vt & vs & Hvt & Hvs & Hr).
          iApply (source_ret); try done.
          iApply (target_ret); try done.
          iApply (both_ret). iApply Hpost.
          iExists I. iFrame. by iPureIntro.

        - by iApply (source_fail).
      }
    }
    iExists _, _, _, _, _, _, _. iFrame. iPureIntro.
    split_and!; try done. by apply init_same_bank.
  Qed.
End remove_nop.
