From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations Require Export FreeSim.

From RSL.Logic Require Export BI.
From RSL.Logic Require Import rPropDef.

Section FSimRules.
  Context {Λₜ Λₛ: lang}.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation fsim := (fsim WfNat WfNat Pₜ Pₛ).
  Abbreviation fsim_lfp := (fsim_lfp WfNat WfNat Pₜ Pₛ).
  Abbreviation post := (value Λₜ -> value Λₛ -> rProp).

  Implicit Types (C: Chain fsim_lfp) (ϕ: post).

  Definition sim_lfp C st j i ss ϕ : rProp :=
    {|
      rProp_holds mt ms :=
        let Ψ '(vt, mt) '(vs, ms) := rProp_holds (ϕ vt vs) mt ms in
        fsim_lfp (elem C) Ψ (st, mt) j i (ss, ms)
    |}.

  Definition sim st j i ss ϕ : rProp :=
    {|
      rProp_holds mt ms :=
        let Ψ '(vt, mt) '(vs, ms) := rProp_holds (ϕ vt vs) mt ms in
        fsim Ψ (st, mt) j i (ss, ms)
    |}.

  Notation
    "'[' C ']' st '<{' j ',' i '}=' ss '{{' Q '}}'" :=
    (sim_lfp C st j i ss Q%I)
      (at level 0, st at level 0, ss at level 0, no associativity).

  Notation
    "st '<{' j ',' i '}=' ss '{{' Q '}}'" :=
    (sim st j i ss Q%I)
      (at level 1, ss at level 1, no associativity).

  Lemma fsim_in_chain st j i ss ϕ:
    (∀ C, [C] st <{j, i}= ss {{ ϕ }}) -∗
    st <{j, i}= ss {{ ϕ }}.
  Proof using Type.
    unseal.
    intros ? ? [-> ->] mt ms _ _ H.
    rewrite !map_empty_union.
    unfold sim, sim_lfp, fsim.
    apply (gfp_prop).
    intros C. simpl.
    apply (b_chain C), H.
  Qed.

  Lemma final C st j i ss ϕ:
    ∀ vt vs,
    ⌜is_value st = Some vt⌟ -∗
    ⌜is_value ss = Some vs⌟ -∗
    ϕ vt vs -∗
    [C] st <{j, i}= ss {{ ϕ }}.
  Proof using Type.
    unseal.
    intros vt vs ? ? [-> ->].
    intros ? ? _ _ [[-> ->] Ht].
    intros ? ? _ _ [[-> ->] Hs].
    intros mt ms _ _ Hp. rewrite !map_empty_union.
    apply FRelated.
    eexists _, _. split_and!.
    - simpl. by rewrite Ht.
    - simpl. by rewrite Hs.
    - assumption.
  Qed.

  Lemma sim_mono C st j i ss ϕ:
    ∀ j' i' ϕ',
    □ (∀ vt vs, ϕ' vt vs -∗ ϕ vt vs) -∗
    ⌜j' ⊑ j⌟ -∗
    ⌜i' ⊑ i⌟ -∗
    [C] st <{j', i'}= ss {{ ϕ' }} -∗
    [C] st <{j, i}= ss {{ ϕ }}.
  Proof using Type.
    revert st j i ss ϕ.
    unseal. unfold sim_lfp.
    apply tower.
    { intros P Hp. do 30 intro. intros Hinf Q Hq.
      eapply (Hp _ Hq); eauto. by apply Hinf. }
    clear C. intros C CIH.
    intros st j i ss ϕ j' i' ϕ' ? ? [-> ->] mtP msP _ _ [[-> ->] Hϕ].
    intros ? ? _ _ [[-> ->] Hj] ? ? _ _ [[-> ->] Hi].
    intros mt ms _ _ H.
    simpl in H, Hj, Hi, Hϕ.
    remember (st, mt : memory) as t eqn:Ht.
    remember (ss, ms : memory) as s eqn:Hs.
    revert i j st mt ss ms Hj Hi Hϕ CIH Ht Hs.
    induction H as
      [ t j' i' s Hfin
      | t j' i' s Hstuck
      | t j' i'' i' s s' Hstep Hsim IHs
      | t j' i' s Hprogress IHt
      | t j' j'' i' i'' s Ht Hs Hgfp ].
    - intros i j st mt ss ms Hj Hi Hϕ _ -> ->.
      apply FRelated.
      destruct Hfin as ([] & [] &
                          (vt & Het & Hft)%is_final_Some &
                          (vs & Hes & Hfs)%is_final_Some & Hfin). subst.
      inv Het.
      eexists _, _. split_and!.
      + unfold is_final. by rewrite Hft.
      + unfold is_final. by rewrite Hfs.
      + apply Hϕ.
        * by rewrite !map_empty_union.
        * by rewrite !map_empty_union; apply map_disjoint_empty_r.
        * by rewrite !map_empty_union; apply map_disjoint_empty_r.
        * assumption.
    - intros i j st mt ss ms Hj Hi Hϕ _ -> ->.
      apply FSourceStuck. by rewrite !map_empty_union.
    - intros i j st mt ss ms Hj Hi Hϕ CIH -> ->.
      destruct s' as [ss' ms'].
      eapply FSourceSteps with (s' := (ss', ∅ ∪ ∅ ∪ ∅ ∪ ∅ ∪ ms')) (i' := i').
      { by rewrite !map_empty_union. }
      by apply IHs.
    - intros i j st mt ss ms Hj Hi Hϕ CIH -> ->.
      apply FTargetSteps. { by rewrite !map_empty_union. }
      intros [st' mt'] Ht'.
      rewrite !map_empty_union in Ht'.
      apply IHt in Ht' as (j'' & Hsim & IH).
      exists j''.
      replace mt' with (∅ ∪ ∅ ∪ ∅ ∪ ∅ ∪ mt') by now rewrite !map_empty_union.
      by apply IH.
    - intros i j st mt ss ms Hj Hi Hϕ CIH -> ->.
      destruct Hj as [Hj | ->], Hi as [Hi | ->];
      (eapply FProgress; try done; eapply CIH; clear CIH; try done);
      try (rewrite !map_empty_union; apply map_disjoint_empty_r);
      (split; [done | simpl]); auto; now left.
  Qed.

  Lemma coind C Inv:
    □ (∀ C st j i ss ϕ,
       □ (∀ st' j' i' ss' ϕ',
            ⌜j ⊏ j'⌟ -∗
            ⌜i ⊏ i'⌟ -∗
            Inv st' j i ss' ϕ' -∗
            [C] st' <{j', i'}= ss' {{ ϕ' }}) -∗
       Inv st j i ss ϕ -∗
       [C] st <{j, i}= ss {{ ϕ }}) -∗
    ∀ st j i ss ϕ,
    Inv st j i ss ϕ -∗
    [C] st <{j, i}= ss {{ ϕ }}.
  Proof using Type.
    unseal. unfold sim_lfp.
    intros ? ? [-> ->] ? ? _ _ [[-> ->] RIH].
    apply tower.
    { intros P Hp. do 9 intro. intros Hinf Q Hq. by apply (Hp _ Hq). }
    clear C. intros C CIH.
    intros st j i ss ϕ mtI msI _ _ HI. simpl.
    apply RIH; clear RIH.
    - by split.
    - easy.
    - easy.
    - split; [done |]. simpl.
      intros ? ? [-> ->] st' i' j' ss' ϕ'.
      intros ? ? _ _ [[-> ->] Hj].
      intros ? ? _ _ [[-> ->] Hi].
      intros mt ms _ _ HInv.
      eapply FProgress; [done | done |].
      apply CIH; auto; by rewrite !map_empty_union; apply map_disjoint_empty_r.
    - by rewrite !map_empty_union; apply map_disjoint_empty_r.
    - by rewrite !map_empty_union; apply map_disjoint_empty_r.
    - easy.
  Qed.

  Definition hoare P st ss Q : rProp :=
    □ (∀ ϕ,
         P -∗
         (∀ vt vs, Q vt vs -∗ ϕ vt vs) -∗
         st <{0, 0}= ss {{ϕ}})%I.

  Notation
    "'{{' P '}}' st '≲' ss '{{' Q '}}'" :=
    (hoare P%I st ss Q%I)
      (at level 0, st at level 0, ss at level 0, no associativity).

  Lemma frame P1 P2 st ss Q :
    {{ P1 }} st ≲ ss {{ Q }} -∗
    {{ P1 ∗ P2 }} st ≲ ss {{ fun vt vs => Q vt vs ∗ P2 }}.
  Proof using Type.
    iIntros "#H !>" (ϕ) "[H1 H2] Hp".
    iApply ("H" with "H1").
    iIntros (vt vs) "Hq".
    iApply "Hp". iFrame.
  Qed.

  Lemma consequence C P st ss Q :
    ∀ P' Q',
    □ (P -∗ P') -∗
    □ (∀ vt vs, Q' vt vs -∗ Q vt vs) -∗
    {{ P' }} st ≲ ss {{ Q' }} -∗
    {{ P }} st ≲ ss {{ Q }}.
  Proof using Type.
    iIntros (P' Q') "#HP #HQ #H !>".
    iIntros (ϕ) "Hpre Hpost".
    iApply ("H" with "[Hpre] [Hpost]").
    - by iApply "HP".
    - iIntros (vt vs) "HQ'".
      iApply "Hpost".
      by iApply "HQ".
  Qed.
End FSimRules.
