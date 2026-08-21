From RSL Require Import Prelude.

From Coinduction Require Export tower.

From RSL.Logic Require Export BI.
From RSL.Simulations Require Export FreeSim.

From RSL.Logic Require Import rPropDef Tactic.

Program Definition sim_def {Λt Λs J I} Pt Ps C t j i s Q : rProp :=
  {|
    rProp_holds mt ms :=
      let Ψ vt vs := rProp_holds (Q vt vs : rProp)
      in elem (C: Chain (@fsim_lfp Λt Λs J I Pt Ps)) Ψ (t, mt) j i (s, ms)
  |}.

Definition sim {Λt Λs J I} Pt Ps C t j i s Q : rProp :=
  ∀ P, P -∗ @sim_def Λt Λs J I Pt Ps C t j i s (fun vt vs => Q vt vs ∗ P).

Notation
  "'[' Pt ',' Ps ',' C ']' t '<{' j ',' i '}=' s '{{' Q '}}'" :=
  (sim Pt Ps C t j i s Q%I)
    (at level 0, t at level 0, s at level 0, no associativity).

Section SimRules.
  Context {Λt Λs: lang} {J I: WfRel}.
  Context {Pt: prog Λt} {Ps: prog Λs}.
  Context {C: Chain (fsim_lfp J I Pt Ps)}.

  Implicit Types (t: state Λt) (j: J) (i: I) (s: state Λs)
    (Q: value Λt -> value Λs -> rProp).

  Lemma final t j i s Q vt vs:
    is_value t = Some vt ->
    is_value s = Some vs ->
    Q vt vs -∗
    [Pt, Ps, C] t <{j, i}= s {{ Q }}.
  Proof using Type.
    intros Ht Hs.
    unfold sim. unseal.
    intros ? ? [-> ->] mtQ msQ _ _ Hq. smap.
    intros W mtW msW Hdt Hds HW. simpl.
    apply chain_related.
    eexists _, _, _, _. split_and!; simpl.
    - by rewrite Ht.
    - by rewrite Hs.
    - exists mtQ, msQ, mtW, msW. by split_and!.
  Qed.

  Lemma sim_mono st j i ss Q j' i' Q':
    (∀ vt vs, Q' vt vs -∗ Q vt vs) -∗
    ⌜j ⊑ j'⌟ -∗
    ⌜i ⊑ i'⌟ -∗
    [Pt, Ps, C] st <{j, i}= ss {{ Q' }} -∗
    [Pt, Ps, C] st <{j', i'}= ss {{ Q }}.
  Proof using Type.
    unfold sim. unseal.
    intros ? ? [-> ->].
    intros mtQ msQ _ _ HQ.
    intros ? ? _ _ [[-> ->] Hj].
    intros ? ? _ _ [[-> ->] Hi].
    intros mt ms ? ? Hsim.
    intros W mtW msW ? ? HW. smap.
    simpl in *. decompose_map_disjoint.
    eapply chain_mono.
    4:{
      replace (mtQ ∪ mt ∪ mtW) with (mt ∪ (mtQ ∪ mtW)).
      2:{ smap. f_equal. by apply map_union_comm. }
      replace (msQ ∪ ms ∪ msW) with (ms ∪ (msQ ∪ msW)).
      2:{ smap. f_equal. by apply map_union_comm. }
      apply Hsim.
      - solve_map_disjoint.
      - solve_map_disjoint.
      - instantiate (1 := {| rProp_holds mt ms :=
                              mt = (mtQ ∪ mtW) ∧
                              ms = (msQ ∪ msW) |}).
        simpl. by split.
    }
    - simpl. intros vt vs mt' ms'.
      intros (mtQ' & msQ' & ? & ? & ? & ? & <- & <- & HQ' & [-> ->]).
      decompose_map_disjoint.
      exists (mtQ ∪ mtQ'), (msQ ∪ msQ'), mtW, msW.
      split_and!.
      + solve_map_disjoint.
      + solve_map_disjoint.
      + smap. f_equal. by apply map_union_comm.
      + smap. f_equal. by apply map_union_comm.
      + by apply HQ.
      + done.
    - done.
    - done.
  Qed.

  Definition SInv : Type :=
    state Λt -> J -> I -> state Λs ->
    (value Λt -> value Λs -> rProp) -> rProp.

  Lemma coind (Inv : SInv) st j i ss Q:
    □ (∀ C st j i ss Q,
       □ (∀ st' j' i' ss' Q',
            ⌜j ⊏ j'⌟ -∗
            ⌜i ⊏ i'⌟ -∗
            Inv st' j i ss' Q' -∗
            [Pt, Ps, C] st' <{j', i'}= ss' {{ Q' }}
       ) -∗
       Inv st j i ss Q -∗
       [Pt, Ps, C] st <{j, i}= ss {{ Q }}
    ) -∗
    Inv st j i ss Q -∗
    [Pt, Ps, C] st <{j, i}= ss {{ Q }}.
  Proof using Type.
    unfold sim. unseal.
    intros ? ? [-> ->].
    intros ? ? _ _ [[-> ->] RIH].
    intros mt ms _ _ Hinv.
    intros W mtW msW Hdt Hds HW.
    smap. unfold sim_def. simpl.
    revert st j i ss Q mt ms Hinv W mtW msW Hdt Hds HW.
    apply tower.
    { intros P Hp st j i ss Q mt ms Hinv W mtW msW Hdt Hds HW ? Hq. by apply Hp. }
    clear C.
    intros C CIH st j i ss Q mt ms Hinv W mtW msW Hdt Hds HW.
    replace (mt) with (∅ ∪ ∅ ∪ ∅ ∪ mt) by smap.
    replace (ms) with (∅ ∪ ∅ ∪ ∅ ∪ ms) by smap.
    apply RIH; clear RIH.
    - done.
    - done.
    - split; [done |]. simpl.
      intros st' i' j' ss' ϕ'.
      intros ? ? _ _ [[-> ->] Hj].
      intros ? ? _ _ [[-> ->] Hi].
      intros mt' ms' _ _ HInv.
      intros W' mtW' msW' Hdt' Hds' HW'.
      eapply FProgress; [done | done |].
      apply CIH; by smap.
    - by smap; apply map_disjoint_empty_r.
    - by smap; apply map_disjoint_empty_r.
    - done.
    - by smap.
    - by smap.
    - done.
  Qed.

  Lemma sim_frame t s j i Q F:
    F -∗
    [Pt, Ps, C] t <{j, i}= s {{ Q }} -∗
    [Pt, Ps, C] t <{j, i}= s {{ fun vt vs => Q vt vs ∗ F }}.
  Proof using Type.
    iIntros "HF Hsim".
    iApply (sim_mono with "[HF] [//] [//] Hsim").
    by iIntros (vt vs) "$".
  Qed.
End SimRules.

Arguments SInv : clear implicits.
