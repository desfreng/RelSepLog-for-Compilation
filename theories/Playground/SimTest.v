From RSL Require Import Prelude.

From stdpp Require Import strings.
From stdpp Require Import gmap.
From stdpp Require Import tactics.

From RSL Require Import Simulations.FreeSim.
From RSL Require Import Simulations.FreeSimRules.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.Semantics.

From RSL Require Import RTL.SimRules.
From RSL Require Import RTL.TargetRules.
From RSL Require Import RTL.SourceRules.

Import RTLNotations.

Section T.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ : prog Λₜ) (Pₛ : prog Λₛ).

  Abbreviation fsim := (fsim WfNat WfNat Pₜ Pₛ).

  Let reg_n : reg := 1.
  Let reg_res : reg := 2.
  Let reg_one : reg := 3.
  Let reg_addr : reg := 4.

  Definition fact_bad : function :=
    {|
      fn_name := "fact"%string;
      fn_regs := [reg_n; reg_addr];
      fn_entrypoint := 0;
      fn_code :=
        <<{{
              0: reg_res := #1 -> 1;
              1: !reg_addr := reg_res -> 2;
              2: if reg_n then goto 6 else goto 3;
              3: reg_res := reg_res * reg_n -> 4;
              4: reg_one := !reg_addr -> 5;
              5: reg_n := reg_n - reg_one -> 2;
              6: ret reg_res;
          }}>>;
      fn_regs_no_dup := eq_refl;
    |}.

  Definition fact_good : function :=
    {|
      fn_name := "fact"%string;
      fn_regs := [reg_n; reg_addr];
      fn_entrypoint := 0;
      fn_code :=
        <<{{
              0: reg_res := #1 -> 1;
              1: !reg_addr := reg_res -> 2;
              2: reg_one := #1 -> 3;
              3: if reg_n then goto 6 else goto 4;
              4: reg_res := reg_res * reg_n -> 5;
              5: reg_n := reg_n - reg_one -> 3;
              6: ret reg_res;
        }}>>;
      fn_regs_no_dup := eq_refl;
    |}.

  Notation
    "'[' C ']' st '<{' j ',' i '}=' ss '{{' Q '}}'" :=
    (sim Pₜ Pₛ C st j i ss Q%I)
      (at level 0, no associativity).

  Notation
    "'[' C ']' '{{' P '}}' st  '<{' j ',' i '}=' ss '{{' Q '}}'" :=
    (hoare Pₜ Pₛ C P%I st j i ss Q%I)
      (at level 0, no associativity).

  Local Definition inv l v ψ st ss : rlogic :=
    ∃ ρₜ ρₛ,
      ⌜st = State fact_good 3 ρₜ⌟ ∗
      ⌜ss = State fact_bad 2 ρₛ⌟ ∗
      (∀ vt vs : val, ⌜vt = vs⌝ ∗ l ₛ~ₜ l -∗ ψ vt vs) ∗
      ⌜∀ r, ~In r [reg_one; reg_addr] -> ρₜ @ r <=> ρₛ @ r⌟ ∗
      ⌜ρₜ @ reg_one ⇒ v⌟ ∗
      ⌜ρₛ @ reg_addr ⇒ l⌟ ∗
      l →ₛ v ∗
      l →ₜ v.

  Ltac close_hyp :=
    match goal with
    | [ |- ?f @ ?pc is _] => reflexivity
    | [ |- ?ρ @ ?l ⇒ _ ] => simregs
    | [ |- eval_op ?op ?vals = Some _ ] => reflexivity
    | [ |- (if _ then _ else _) = _ ] => reflexivity
    | [ |- context [(_ →ₜ _)%I] ] => try iAssumption
    | [ |- ?goal ] => idtac goal
    end.

  Lemma fact_same ρₜ ρₛ:
    ∀ addr,

    (∀ r, ρₜ @ r <=> ρₛ @ r) ->
    ρₛ @ reg_addr ⇒ addr ->

    ⊢
      [fsim] {{ addr ₛ~ₜ addr }}
      State fact_good 0 ρₜ <{0, 0}= State fact_bad 0 ρₛ
      {{ fun vₜ vₛ =>
           ⌜vₜ = vₛ⌝ ∗
           addr ₛ~ₜ addr
      }}.
  Proof using Type.
    intros addr Hsame Haddrs'.
    iIntros "!>" (ψ) "(%v & Ht & Hs) Hpost".

    iApply (source_op). all: close_hyp.
    iIntros (? Hv); inv Hv.
    iApply (target_op). all: close_hyp.

    destruct (Hsame reg_addr) as (? & Haddrs & Haddrt). simregs.

    iApply (source_store with "Hs"). all: close_hyp.
    iIntros "Hs".
    iApply (target_store with "Ht"). all: close_hyp.
    iIntros "Ht".

    iApply (target_op). all: close_hyp.
    iApply (coind Pₜ Pₛ (inv addr 1)).
    {
      clear. iIntros "!>" (R st i j ss) "#CIH".
      iIntros "(%ρₜ & %ρₛ & -> & -> & Hpost & %Hsame & %Hone & %Haddr & Hs & Ht)".

      destruct (Hsame reg_n) as (n & Htn & Hsn). 1: (cbv; lia).
      destruct (Hsame reg_res) as (r & Htr & Hsr).  1: (cbv; lia).

      iApply (source_if). all: close_hyp.
      iApply (target_if). all: close_hyp.

      destruct (n =? 0)%Z.
      {
        iApply (both_ret). all: close_hyp.
        iApply ("Hpost"). now iFrame.
      }

      iApply (source_op). all: close_hyp.
      iIntros (? Hv); inv Hv.
      iApply (target_op). all: close_hyp.

      iApply (source_load with "Hs"). all: close_hyp.
      iIntros "Hs".

      iApply (source_op). all: close_hyp.
      iIntros (? Hv); inv Hv.

      iApply (target_op). all: close_hyp.

      iApply "CIH"; try (iPureIntro; by lia).
      iExists _, _. iFrame. iPureIntro.
      split. { reflexivity. }
      split. { reflexivity. }
      repeat split.
      - intros r' Hr.
        destruct (Hsame r' Hr) as (? & ? & ?).
        rewrite !not_in_cons in Hr.
        destruct Hr as (? & ? & _).

        destruct (in_dec Nat.eq_dec r' [reg_n; reg_res])
          as [[<- | [<- | ?]] | Hr].
        + eexists. split; simregs.
        + eexists. split; simregs.
        + contradiction.
        + rewrite !not_in_cons in Hr.
          destruct Hr as (? & ? & _).
          eexists. split; simregs.
      - simregs.
      - simregs.
    }
    iExists _, _. iFrame. iPureIntro.
    split. { reflexivity. }
    split. { reflexivity. }
    repeat split.
    - intros r Hr.
      rewrite !not_in_cons in Hr.
      destruct Hr as (? & ? & _).
      destruct (in_dec Nat.eq_dec r [reg_res])
        as [[-> | ?] | Hr].
      + eexists. split; simregs.
      + contradiction.
      + rewrite !not_in_cons in Hr.
        destruct Hr as (? & _).
        destruct (Hsame r) as (? & ? & ?).
        eexists. split; simregs.
    - simregs.
    - simregs.
  Qed.

End T.

(* Memcopy avec déroulage de boucle ? *)
(* Optimisations des nop ? *)
(* Inlining à la main ? *)
