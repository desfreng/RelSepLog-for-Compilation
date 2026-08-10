From RSL Require Import Prelude.

From Coinduction Require Export tower.

From RSL.Logic Require Export BI.
From RSL.Simulations Require Export FreeSim.

From RSL.Logic Require Import rPropDef Tactic.

Program Definition sim_lfp {Λt Λs J I} Pt Ps C st j i ss Q : rProp :=
  {|
    rProp_holds mt ms :=
      let Ψ vt vs := rProp_holds (Q vt vs : rProp)
      in elem (C: Chain (@fsim_lfp Λt Λs J I Pt Ps)) Ψ (st, mt) j i (ss, ms)
  |}.

Notation
  "'[' Pt ',' Ps ',' C ']' st '<{' j ',' i '}=' ss '{{' Q '}}'" :=
  (sim_lfp Pt Ps C st j i ss Q%I)
    (at level 0, st at level 0, ss at level 0, no associativity).

Section SimRules.
  Context {Λt Λs: lang} {J I: WfRel}.
  Context {Pt: prog Λt} {Ps: prog Λs}.
  Context {C: Chain (fsim_lfp J I Pt Ps)}.

  Implicit Types
    (st: pstate Λt) (j: J) (i: I) (ss: pstate Λs) (Q: value Λt -> value Λs -> rProp).

  Lemma final st j i ss Q vt vs:
    is_value st = Some vt ->
    is_value ss = Some vs ->
    Q vt vs -∗
    [Pt, Ps, C] st <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros Ht Hs.
    unseal. intros ? ? [-> ->] mt ms _ _ Hp. smap.
    apply chain_related.
    eexists _, _, _, _. split_and!.
    - simpl. by rewrite Ht.
    - simpl. by rewrite Hs.
    - simpl. assumption.
  Qed.

  Lemma sim_mono st j i ss Q j' i' Q':
    □ (∀ vt vs, Q' vt vs -∗ Q vt vs) -∗
    ⌜j ⊑ j'⌟ -∗
    ⌜i ⊑ i'⌟ -∗
    [Pt, Ps, C] st <{j, i}= ss {{ Q' }} -∗
    [Pt, Ps, C] st <{j', i'}= ss {{ Q }}.
  Proof using Type.
    unseal.
    intros ? ? [-> ->].
    intros ? ? _ _ [[-> ->] HQ].
    intros ? ? _ _ [[-> ->] Hj].
    intros ? ? _ _ [[-> ->] Hi].
    intros mt ms _ _ Hsim. smap.
    simpl in *.
    eapply chain_mono; last done.
    - intros vt vs mt' ms' H.
      replace (mt') with (∅ ∪ mt') by smap.
      replace (ms') with (∅ ∪ ms') by smap.
      apply HQ.
      + by apply map_disjoint_empty_r.
      + by apply map_disjoint_empty_r.
      + assumption.
    - done.
    - done.
  Qed.

  Definition SInv : Type :=
    pstate Λt -> J -> I -> pstate Λs ->
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
    unseal.
    intros ? ? [-> ->]. smap.
    intros ? ? _ _ [[-> ->] RIH]. smap.
    intros mt ms _ _ Hinv. smap.
    unfold sim_lfp. simpl.
    revert st j i ss Q mt ms Hinv.
    apply tower.
    { intros P Hp st j i ss Q mt ms Hinv ? Hq. by apply Hp. }
    clear C.
    intros C CIH st j i ss Q mt ms Hinv.
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
      eapply FProgress; [done | done |].
      apply CIH. by smap.
    - by smap; apply map_disjoint_empty_r.
    - by smap; apply map_disjoint_empty_r.
    - done.
  Qed.
End SimRules.

Arguments SInv : clear implicits.
