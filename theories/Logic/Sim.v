From RSL Require Import Prelude.

From Coinduction Require Export tower.

From RSL.Logic Require Export BI.
From RSL.Simulations Require Export FreeSim.

From RSL.Logic Require Import rPropDef Tactic.

Program Definition sim_lfp {Λt Λs J I} Pt Ps C st j i ss Q : rProp :=
  {|
    rProp_holds mt ms :=
      let Ψ : value Λt * memory -> value Λs  * memory -> Prop :=
        fun '(vt, mt) '(vs, ms) => rProp_holds (Q vt vs : rProp) mt ms
      in
      @fsim_lfp Λt Λs J I Pt Ps
        (elem (C: Chain (fsim_lfp _ _ Pt Ps)))
        Ψ (st, mt) j i (ss, ms)
  |}.

Notation
  "'[' Pt ',' Ps ',' C ']' st '<{' j ',' i '}=' ss '{{' Q '}}'" :=
  (sim_lfp Pt Ps C st j i ss Q%I)
    (at level 0, st at level 0, ss at level 0, no associativity).

Section SimRules.
  Context {Λt Λs: lang} {J I: WfRel}.

  Context {Pt: prog Λt} {Ps: prog Λs}.
  Context {C: Chain (fsim_lfp J I Pt Ps)}.
  Context {st: pstate Λt} {j: J} {i: I} {ss: pstate Λs}.
  Context {Q: value Λt → value Λs → rProp}.

  Lemma final vt vs:
    is_value st = Some vt ->
    is_value ss = Some vs ->
    Q vt vs -∗
    [Pt, Ps, C] st <{j, i}= ss {{ Q }}.
  Proof using Type.
    intros Ht Hs.
    unseal. simpl. unseal.
    intros ? ? [-> ->] mt ms _ _ Hp. smap.
    apply FRelated.
    eexists _, _. split_and!.
    - simpl. by rewrite Ht.
    - simpl. by rewrite Hs.
    - simpl. assumption.
  Qed.

  Lemma sim_mono j' i' Q':
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
    revert mt ms j j' i i' st ss Q Q' HQ Hj Hi Hsim.
    unfold sim_lfp.
    eapply (tower).
    { intros P Hp.
      intros mt ms j j' i i' st ss Q Q' HQ Hj Hi.
      intros Hinf P' Hp'.
      eapply (Hp _ Hp'); eauto. by eapply Hinf.
    }
    clear C. intros C CIH mt ms j j' i i' st ss Q Q' HQ Hj Hi Hsim.
    simpl in Hsim.
    remember (st, mt : memory) as t eqn:Ht.
    remember (ss, ms : memory) as s eqn:Hs.
    revert i' j' st mt ss ms Hj Hi HQ CIH Ht Hs.
    induction Hsim as
      [ t j' i' s Hfin
      | t j' i' s Hstuck
      | t j' i'' i' s s' Hstep Hsim IHs
      | t j' i' s Hprogress IHt
      | t j' j'' i' i'' s Ht Hs Hgfp ].
    - intros i j st mt ss ms Hj Hi Hϕ _ -> ->.
      apply FRelated.
      destruct Hfin as ([? mt'] & [? ms'] &
                          (vt & Het & Hft)%is_final_Some &
                          (vs & Hes & Hfs)%is_final_Some & Hfin). subst.
      inv Het.
      eexists _, _. split_and!.
      + unfold is_final. by rewrite Hft.
      + unfold is_final. by rewrite Hfs.
      + simpl.
        replace (mt') with (∅ ∪ mt') by smap.
        replace (ms') with (∅ ∪ ms') by smap.
        apply Hϕ.
        * by apply map_disjoint_empty_r.
        * by apply map_disjoint_empty_r.
        * assumption.
    - intros i j st mt ss ms Hj Hi Hϕ _ -> ->.
      by apply FSourceStuck.
    - intros i j st mt ss ms Hj Hi Hϕ CIH -> ->.
      destruct s' as [ss' ms'].
      eapply FSourceSteps.
      + done.
      + by apply IHs.
    - intros i j st mt ss ms Hj Hi Hϕ CIH -> ->.
      apply FTargetSteps.
      { done. }
      intros [st' mt'] Ht'.
      apply IHt in Ht' as (j'' & Hsim & IH).
      exists j''. by apply IH.
    - intros i j st mt ss ms Hj Hi Hϕ CIH -> ->.
      destruct Hj as [Hj | ->], Hi as [Hi | ->];
      (eapply FProgress;
       [ done
       | done
       | eapply CIH; [ done | | | done ]]);
      reflexivity || now left.
  Qed.

  Lemma coind Inv:
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
    intros ? ? [-> ->] ? ? _ _ [[-> ->] RIH].
    revert st j i ss Q. unfold sim_lfp.
    apply tower.
    { intros P Hp. do 9 intro. intros Hinf P' Hq. by apply (Hp _ Hq). }
    clear C.
    intros C CIH st j i ss Q.
    intros mtI msI _ _ HI.
    apply RIH; clear RIH.
    - by split.
    - easy.
    - split; [done |]. simpl.
      intros st' i' j' ss' ϕ'.
      intros ? ? _ _ [[-> ->] Hj].
      intros ? ? _ _ [[-> ->] Hi].
      intros mt ms _ _ HInv.
      eapply FProgress; [done | done |].
      apply CIH.
      + by smap; apply map_disjoint_empty_r.
      + by smap; apply map_disjoint_empty_r.
      + done.
    - by smap; apply map_disjoint_empty_r.
    - by smap; apply map_disjoint_empty_r.
    - easy.
  Qed.

End SimRules.
