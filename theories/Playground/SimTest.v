From RSL Require Import RelLogic Prelude.

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
    "'[' C ']' ρ '⊢' ft '@' pct  '<{' j ',' i '}=' fs '@' pcs '{{' Q '}}'" :=
    (sim Pₜ Pₛ C ρ ft pct j i fs pcs Q%rlogic)
      (at level 0, ft at level 0, fs at level 0, no associativity).

  Notation
    "'[' C ']' ρ '⊢' '{{' P '}}' ft '@' pct  '<{' j ',' i '}=' fs '@' pcs '{{' Q '}}'" :=
    (hoare Pₜ Pₛ C ρ P%rlogic ft pct j i fs pcs Q%rlogic)
      (at level 0, ft at level 0, fs at level 0, no associativity).

  Lemma inv_proof ρₜ ρₛ P : ∀ l v,
    [fsim] (ρₜ, ρₛ) ⊢
    {{ (fun ρₜ ρₛ =>
          ⌜∀ r, ~In r [reg_one; reg_addr] -> ρₜ @ r <=> ρₛ @ r⌝ ∗
          ⌜ρₜ @ reg_one ⇒ v⌝ ∗
          ⌜ρₛ @ reg_addr ⇒ l⌝ ∗
          l →ₛ v ∗ P
       ) ρₜ ρₛ
    }}
      fact_good @ 3 <{0, 0}= fact_bad @ 2
    {{ fun vₜ vₛ =>
         ⌜vₜ = vₛ⌝ ∗
         l →ₛ v ∗
         P
    }}.
  Proof using Type.
    intros l v.
    apply coind.
    clear.
    intros R ρₜ ρₛ CIH.
    apply ipure. intros Hsame.
    apply ipure. intros Hone.
    apply ipure. intros Haddr.

    destruct (Hsame reg_n) as (n & Htn & Hsn). 1: (cbv; lia).
    destruct (Hsame reg_res) as (r & Htr & Hsr).  1: (cbv; lia).

    eapply source_if; [ reflexivity | simregs | reflexivity |].
    eapply target_if; [ reflexivity | simregs | reflexivity |].

    destruct (n =? 0)%Z.
    {
      intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

      destruct Hpre as (mtv & msv & mtP & msP & ? & ? & ? & ? & Hs & HP).
      destruct Hs as (Ht & (l' & Hl & Hs)).
      destruct Hemp as (-> & ->).

      eapply both_ret.
      - reflexivity.
      - reflexivity.
      - simregs.
      - simregs.
      - rewrite (map_union_comm mtPost) by solve_map_disjoint.
        rewrite (map_union_comm msPost) by solve_map_disjoint.
        apply Hpost; try solve_map_disjoint.
        eexists ∅, ∅, mtP, (msv ∪ msP). repeat split.
        + solve_map_disjoint.
        + solve_map_disjoint.
        + subst. now rewrite !map_union_empty, !map_empty_union.
        + subst. now rewrite !map_union_empty, !map_empty_union.
        + exists ∅, msv, mtP, msP. repeat split.
          * solve_map_disjoint.
          * solve_map_disjoint.
          * apply map_empty_union.
          * now exists l'.
          * assumption.
    }
    eapply source_op; [ reflexivity | simregs | simpl eval_op; intros ? Hv; inv Hv ].

    eapply target_op; [ reflexivity | simregs | reflexivity | ].
    eapply target_op; [ reflexivity | simregs | reflexivity | ].

    eapply source_load; [reflexivity | simregs | ].
    eapply source_op; [ reflexivity | simregs | simpl eval_op; intros ? Hv; inv Hv ].

    eapply consequence.
    3:{ apply CIH; lia. }
    - intros mt ms H.
      apply sep_pure_left.
      {
        intros r' Hr.
        destruct (Hsame r' Hr) as (? & ? & ?).
        rewrite !not_in_cons in Hr.
        destruct Hr as (? & ? & _).

        destruct (in_dec Nat.eq_dec r' [reg_n; reg_res])
          as [[<- | [<- | ?]] | Hr].
        - eexists. split; simregs.
        - eexists. split; simregs.
        - contradiction.
        - rewrite !not_in_cons in Hr.
          destruct Hr as (? & ? & _).
          eexists. split; simregs.
      }
      apply sep_pure_left.
      { simregs. }
      apply sep_pure_left.
      { simregs. }
      easy.
    - now simpl.
  Qed.

  Lemma fact_same ρₜ ρₛ:
    ∀ addr,

    (∀ r, ρₜ @ r <=> ρₛ @ r) ->
    ρₛ @ reg_addr ⇒ addr ->

    [fsim] (ρₜ, ρₛ) ⊢
    {{
        addr ₛ~ₜ addr
    }}
      fact_good @ 0 <{0, 0}= fact_bad @ 0
    {{ fun vₜ vₛ =>
         ⌜vₜ = vₛ⌝ ∗
         addr ₛ~ₜ addr
    }}.
  Proof using Type.
    intros addr Hsame Haddrs'.
    eapply iex. intros v.

    eapply source_op; [ reflexivity | simregs | intros ? Hv; inv Hv ].
    eapply target_op; [ reflexivity | simregs | reflexivity | ].

    destruct (Hsame reg_addr) as (? & Haddrs & Haddrt). simregs.

    eapply consequence.
    { apply sep_comm. }
    { intros. apply entails_refl. }

    eapply source_store; [ reflexivity | simregs | simregs | ].

    eapply consequence.
    { apply sep_comm. }
    { intros. apply entails_refl. }

    eapply target_store; [ reflexivity | simregs | simregs | ].
    eapply target_op; [ reflexivity | simregs | reflexivity | ].

    eapply consequence.
    3: eapply fsim_mono; try apply inv_proof; lia.
    - intros mt ms H.
      apply sep_pure_left.
      {
        intros r Hr.
        rewrite !not_in_cons in Hr.
        destruct Hr as (? & ? & _).

        destruct (in_dec Nat.eq_dec r [reg_res])
          as [[-> | ?] | Hr].
        - eexists. split; simregs.
        - contradiction.
        - rewrite !not_in_cons in Hr.
          destruct Hr as (? & _).
          destruct (Hsame r) as (? & ? & ?).
          eexists. split; simregs.
      }
      apply sep_pure_left. 1: simregs.
      apply sep_pure_left. 1: simregs.
      apply sep_comm. apply H.
    - intros vₜ vₛ. simpl.
      eapply entails_frame_l.
      intros mt ms H. eexists.
      apply sep_comm. apply H.
  Qed.

End T.

(* Memcopy avec déroulage de boucle ? *)
(* Optimisations des nop ? *)
(* Inlining à la main ? *)
