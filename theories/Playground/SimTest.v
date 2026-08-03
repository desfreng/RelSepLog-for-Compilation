From RSL Require Import Prelude.

From RSL.Logic Require Import Logic.
From RSL.RTL Require Import SimRules.

Import RTLNotations.

Section T.
  Let Λₜ : lang := rtl_lang.
  Let Λs : lang := rtl_lang.
  Context (Pt : prog Λₜ) (Ps : prog Λs).

  Abbreviation fsim := (fsim WfNat WfNat Pt Ps).

  Let reg_n : reg := 1.
  Let reg_res : reg := 2.
  Let reg_one : reg := 3.
  Let reg_addr : reg := 4.
  Let reg_cond : reg := 5.

  Definition fact_bad : rtl_function :=
    {|
      fn_name := "fact"%string;
      fn_regs := [reg_n; reg_addr];
      fn_entrypoint := 0;
      fn_code :=
        <<{{
              0: reg_res := #(VInt 1) -> 1;
              1: !reg_addr := reg_res -> 2;
              2: reg_cond := isZ reg_n -> 3;
              3: if reg_cond then goto 7 else goto 4;
              4: reg_res := reg_res * reg_n -> 5;
              5: reg_one := !reg_addr -> 6;
              6: reg_n := reg_n - reg_one -> 2;
              7: ret reg_res;
          }}>>;
      fn_regs_no_dup := eq_refl;
    |}.

  Definition fact_good : rtl_function :=
    {|
      fn_name := "fact"%string;
      fn_regs := [reg_n; reg_addr];
      fn_entrypoint := 0;
      fn_code :=
        <<{{
              0: reg_res := #(VInt 1) -> 1;
              1: !reg_addr := reg_res -> 2;
              2: reg_one := #(VInt 1) -> 3;
              3: reg_cond := isZ reg_n -> 4;
              4: if reg_cond then goto 7 else goto 5;
              5: reg_res := reg_res * reg_n -> 6;
              6: reg_n := reg_n - reg_one -> 3;
              7: ret reg_res;
        }}>>;
      fn_regs_no_dup := eq_refl;
    |}.

  Ltac close_hyp :=
    match goal with
    | [ |- ?f @ ?pc is _] => done
    | [ |- ?ρ @ ?l ⇒ _ ] => try simregs
    | [ |- eval_op ?op ?vals = Some _ ] => done
    | [ |- (if _ then _ else _) = _ ] => done
    | [ |- context [(_ →ₜ _)%I] ] => try iAssumption
    | [ |- context [(_ →ₛ _)%I] ] => try iAssumption
    | [ |- context [mem_inj _ _] ] => try iAssumption
    | [ |- same_val _ _ _ ] => try done
    | [ |- ?goal ] => idtac
    end.

  Definition samer I vt vs : rProp :=
    ∃ I',
      ⌜same_val I vt vs⌟ ∗
      ⌜I ⊆ I'⌟ ∗
      mem_inj I' ∅.

  Local Definition inv lt ls v (st: pstate Λₜ) (j i: nat) (ss: pstate Λs) ψ : rProp :=
    ∃ I ρt ρs,
      mem_inj I {[ (ls, lt) ]} ∗
      ls →ₛ v ∗
      lt →ₜ v ∗
      (∀ vt vs, samer I vt vs -∗ ψ vt vs) ∗
      ⌜
        st = ([], State fact_good 3 ρt) ∧
        ss = ([], State fact_bad 2 ρs) ∧
        ρt @ reg_n <{ I }> ρs @ reg_n ∧
        ρt @ reg_res <{ I }> ρs @ reg_res ∧
        ρt @ reg_one ⇒ v ∧
        ρs @ reg_addr ⇒ VPtr ls ∧
        ρt @ reg_addr ⇒ VPtr lt
      ⌟.

  Lemma fact_same C I :
    ∀ args_t args_s,
    Forall2 (same_val I) args_t args_s ->
    mem_inj I ∅ -∗
    [Pt, Ps, C]
      ([], CallState fact_good args_t)
        <{0, 0}=
      ([], CallState fact_bad args_s)
    {{ samer I }}.
  Proof using Type.
    intros args_t args_s Hsame.
    iIntros "Hinj".
    iApply (source_callstate_exploit).
    iIntros (ρs pc Hlen -> ->).
    iApply (target_callstate); [ by eapply Forall2_length_r | done | done |].

    destruct (init_regs_sound fact_bad args_s) as (ρs & <- & Hs).
    { done. }

    destruct (init_regs_sound fact_good args_t) as (ρt & <- & Ht).
    { by eapply Forall2_length_r. }

    destruct args_s as [|vs_n [|vs_addr []]]; inv Hlen.
    apply Forall2_cons_inv_r in Hsame as (vt_n & ? & Hv & Hsame & ->).
    apply Forall2_cons_inv_r in Hsame as (vt_addr & ? & Hreg & Hsame & ->).
    apply Forall2_nil_inv_r in Hsame as ->.

    eassert (ρs@reg_n ⇒ _) by (by apply Hs with 0).
    eassert (ρt@reg_n ⇒ _) by (by apply Ht with 0).

    eassert (ρs@reg_addr ⇒ _) by (by apply Hs with 1).
    eassert (ρt@reg_addr ⇒  _) by (by apply Ht with 1).

    clear Ht Hs.

    iApply (source_op). all: close_hyp.
    iApply (target_op). all: close_hyp.
    simpl.

    iApply (source_store_exploit). all: close_hyp.
    { by set_solver. }
    iIntros (E' lt ls vt -> -> ->).
    iIntros "Ht Hs Hinj".

    iApply (target_store with "[-Ht] Ht"). all: close_hyp.
    iIntros "Ht".
    simpl.

    iApply (target_op). all: close_hyp.
    simpl.

    iApply (coind (inv lt ls (VInt 1))).
    {
      clear.
      iIntros "!>" (C st j i ss ϕ) "#CIH".
      iIntros "(%I & %ρt & %ρs & Hinj & Hs & Ht & Hpost & %Hinv)".
      destruct Hinv as (-> & -> & Hn & Hres & Hone & Haddr_s & Haddr_t).

      destruct Hn as (vn_t & vn_s & ? & ? & Hsame_n).
      destruct Hres as (vres_t & vres_s & ? & ? & Hsame_res).
      simpl.

      iApply (source_op_exploit). all: close_hyp.
      iIntros (v Hz).
      destruct vn_s as [ vn | | | ], vn_t; inv Hz; inv Hsame_n.

      iApply (target_op). all: close_hyp.
      simpl.

      iApply (source_if). all: close_hyp.
      iApply (target_if). all: close_hyp.
      simpl.

      destruct (vn =? 0)%Z.
      - iApply (source_ret). all: close_hyp.
        iApply (target_ret). all: close_hyp.
        iApply (final); try done.
        iAssert (mem_inj I ∅) with "[Hinj Ht Hs]" as "Hinj".
        {
          replace ∅ with ({[(ls, lt)]} ∖ {[(ls, lt)]} : gset (loc * loc)) by set_solver.
          iApply (inj_release with "Hinj Ht Hs"); by set_solver.
        }
        iApply "Hpost".
        iExists I. iFrame. by iPureIntro.
      -
        iApply (source_op_exploit). all: close_hyp.
        iIntros (? Hv).
        destruct vres_s, vres_t; inv Hv; inv Hsame_res.

        iApply (target_op). all: close_hyp.
        simpl.

        iApply (source_load with "[-Hs] [Hs]"). all: close_hyp.
        iIntros "Hs".

        iApply (source_op). all: close_hyp.
        iApply (target_op). all: close_hyp.
        simpl.

        iApply "CIH"; try (iPureIntro; by lia).
        iExists I, _, _. iFrame. iPureIntro.
        split_and!.
        + reflexivity.
        + reflexivity.
        + eexists _, _. split_and!; simregs || done.
        + eexists _, _. split_and!; simregs || done.
        + simregs.
        + simregs.
        + simregs.
    }
    replace ({[(ls, lt)]} ∪ ∅) with ({[(ls, lt)]} : gset (loc * loc)) by set_solver.
    iExists I, _, _. iFrame.
    iSplit. { by iIntros (? ?) "$". }
    iPureIntro. split_and!.
    - reflexivity.
    - reflexivity.
    - eexists _, _. split_and!; simregs || done.
    - eexists _, _. split_and!; simregs || done.
    - simregs.
    - simregs.
    - simregs.
  Qed.
End T.

(* Memcopy avec déroulage de boucle ? *)
(* Optimisations des nop ? *)
(* Inlining à la main ? *)
