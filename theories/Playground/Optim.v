From RSL Require Import Prelude.

From RSL.Logic Require Import Logic.
From RSL.RTL Require Import SimRules.

Import RTLNotations.

Section T.
  Let Λt : lang := rtl_lang.
  Let Λs : lang := rtl_lang.

  Definition no_opt_fun (fs: rtl_function) : rtl_function :=
    {|
      fn_name := fn_name fs;
      fn_regs := fn_regs fs;
      fn_entrypoint := fn_entrypoint fs;
      fn_code := fn_code fs;
      fn_regs_no_dup := fn_regs_no_dup fs
    |}.

  Lemma no_opt_no_dup {Ps} :
    is_no_dup (fn_name <$> prog_fun_list Ps) = true ->
    is_no_dup (fn_name <$> fmap no_opt_fun (prog_fun_list Ps)) = true.
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

  Lemma no_opt_with_main {Ps} :
    is_Some (find_fun_in_list (prog_fun_list Ps) (prog_main Ps)) ->
    is_Some (find_fun_in_list (no_opt_fun <$> prog_fun_list Ps) (prog_main Ps)).
  Proof using Type.
    unfold find_fun_in_list.
    intros [fmain ([n f] & H & ->)%fmap_Some].
    apply list_find_Some in H as (Hres & Hp & Hfirst).
    rewrite fmap_is_Some.
    eexists (_, _).
    apply list_find_Some. split_and!.
    - apply list_lookup_fmap_Some. by exists f.
    - done.
    - intros j ? (f' & -> & Hin)%list_lookup_fmap_Some Hj. simpl.
      by eapply Hfirst.
  Qed.

  Definition no_opt (Ps: prog Λs) : prog Λt :=
    {|
      prog_fun_list := fmap no_opt_fun (prog_fun_list Ps);
      prog_main := prog_main Ps;
      prog_fun_list_no_dup := no_opt_no_dup (prog_fun_list_no_dup Ps);
      prog_main_exists := no_opt_with_main (prog_main_exists Ps)
    |}.

  Context (Ps : prog Λs).
  Let Pt : prog Λt := no_opt Ps.

  Definition no_opt_inv (st: pstate Λt) (j i: nat) (ss: pstate Λs) ϕ : rProp :=
    ∃ I f pc ρt ρs,
      ⌜st = ([], State (no_opt_fun f) pc ρt)⌟ ∗
      ⌜ss = ([], State f pc ρs)⌟ ∗
      ⌜∀ r, ρt@r <{ I }> ρs@r⌟ ∗
      mem_inj I ∅ ∗
      (∀ vt vs : value rtl_lang,
         (∃ I', ⌜ I ⊆ I' ⌟ ∗ ⌜ same_val I' vt vs ⌟ ∗ mem_inj I' ∅) -∗ ϕ vt vs).

  Definition same_args I valt vals : rProp :=
    ⌜Forall2 (same_val I) valt vals⌟ ∗ mem_inj I ∅.

  Definition samer I vt vs : rProp :=
    ∃ I', ⌜I ⊆ I'⌟ ∗ ⌜same_val I' vt vs⌟ ∗ mem_inj I' ∅.

  Lemma toto_no_opt C f I :
    ⊢ [Pt, Ps, C] {{ same_args I }} (no_opt_fun f) <{0, 0}= f {{ samer I }}.
  Proof using Type.
    iIntros "!>" (valt vals ϕ) "[%Harg Hinj] Hpost".
    iApply (source_callstate_exploit).
    iIntros (ρs pc Hlen -> ->).
    iApply (target_callstate); auto. { by eapply Forall2_length_r. }
    simpl.
    iApply (coind no_opt_inv).
    {
      clear. iIntros "!>" (C st j i ss ϕ) "#CIH".
      iIntros "(%I & %f & %pc & %ρt & %ρs & -> & -> & %Hsame & Hinj & Hpost)".
      destruct ((fn_code f) !! pc)
        as [
          [ pc'
          | op args pc'
          | src dst pc'
          | dst src pc'
          | fn args dst pc'
          | b tpc fpc
          | r
          ]
        |] eqn:Hi.
      - iApply (source_nop). { done. }
        iApply (target_nop). { done. }
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, ρt, ρs. iFrame. iPureIntro. by split_and!.
      - destruct (regbank_never_empty_list ρs args) as [vs].
        destruct (regbank_never_empty_list ρt args) as [vt].
        iApply (source_op_exploit); try done.
        iIntros (v Hv). iApply (target_op).
        { done. }
        { done. }
        { admit. }
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, _, _. iFrame. iPureIntro. split_and!. 1-2: done.
        { admit. }
      - destruct (Hsame src) as (vt & vs & Ht & Hs & Hv).
        iApply (both_load with "[Hpost] Hinj"); try done.
        iIntros (vt' vs' Hv') "Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, _, _. iFrame. iPureIntro. split_and!. 1-2: done.
        { admit. }
      - destruct (Hsame src) as (addrt & addrs & Haddrt & Haddrs & Haddr).
        destruct (Hsame dst) as (dstt & dsts & Hdstt & Hdsts & Hdst).
        iApply (both_store with "[Hpost] Hinj"); try done.
        iIntros "Hinj".
        iApply "CIH"; try (iPureIntro; simpl; lia).
        iExists I, f, _, _, _. iFrame. iPureIntro. by split_and!.
      - destruct (find_fun Ps fn) eqn:Hfn.
        + destruct (regbank_never_empty_list ρs args) as [vs].
          destruct (regbank_never_empty_list ρt args) as [vt].
          iApply (both_call_framed); try done.
          { admit. }
          { admit. }
          { admit. }
          { admit. }
        + iApply (source_call_fails); eauto. iCombine "Hinj Hpost" as "H". iApply "H".
      - admit.
      - admit.
      - iApply (source_fails). { done. }
        iCombine "Hinj Hpost" as "H". iApply "H".
    }
    iExists I, f, _, _, _. iFrame.
    iPureIntro. split_and!.
    - reflexivity.
    - reflexivity.
    - intros r.
      admit.
  Admitted.
End T.
