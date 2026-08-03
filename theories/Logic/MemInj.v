From RSL Require Import Prelude.

From RSL.Logic Require Export PointsTo.
From RSL.Commons Require Export BijSet.

From RSL.Commons Require Import RegisterBank.

Implicit Types (I E: gset (loc * loc)) (lt ls : loc).

Definition related I lt ls := (ls, lt) ∈ I.

Definition same_val I := val_eq (related I).

Definition regbank_same I (ρ1: regbank) (r1: reg) (ρ2: regbank) (r2: reg) :=
  ∃ v1 v2,
    ρ1@r1 ⇒ v1 ∧
    ρ2@r2 ⇒ v2 ∧
    same_val I v1 v2.

Notation "ρ1 @ r1 '<{' I '}>' ρ2 @ r2" :=
  (regbank_same I ρ1 r1%nat ρ2 r2%nat)
    (at level 60, ρ2 at next level, no associativity).

Lemma same_val_mono I I' vt vs :
  I ⊆ I' ->
  same_val I vt vs ->
  same_val I' vt vs.
Proof using Type.
  destruct vt as [], vs as []; simpl; auto.
  unfold related. by auto.
Qed.

Definition sdom E : gset loc := set_map fst E.
Definition tdom E : gset loc := set_map snd E.

Lemma sdom_spec E ls : ls ∈ sdom E <-> ∃ lt, (ls, lt) ∈ E.
Proof using Type.
  rewrite elem_of_map. split.
  - intros ([] & -> & Hin). by eexists.
  - intros (? & ?). by eexists (_, _).
Qed.

Lemma tdom_spec E lt : lt ∈ tdom E <-> ∃ ls, (ls, lt) ∈ E.
Proof using Type.
  rewrite elem_of_map. split.
  - intros ([] & -> & Hin). by eexists.
  - intros (? & ?). by eexists (_, _).
Qed.

Definition mem_inj I E : rProp :=
  (
    ⌜bij_set I⌟ ∗
    ⌜E ⊆ I⌟ ∗
    [∗ set] '(ls, lt) ∈ I,
        if (decide (ls ∈ sdom E))
        then emp
        else
          ∃ vt vs,
            ⌜same_val I vt vs⌟ ∗ lt →ₜ vt ∗ ls →ₛ vs
  )%I.

Lemma inj_empty : ⊢ mem_inj ∅ ∅.
Proof using Type.
  unfold mem_inj.
  iSplit. { iPureIntro. by apply bij_set_empty. }
  iSplit.
  - iPureIntro. intros p Hin. inv Hin.
  - by iApply big_sepS_empty.
Qed.

Lemma inj_insert_exploit I I' E lt ls vt vs :
  I' = {[ (ls, lt) ]} ∪ I ->
  ls ∉ sdom E ->
  lt ∉ tdom E ->
  mem_inj I E -∗
  lt →ₜ vt -∗
  ls →ₛ vs -∗
  ⌜same_val I vt vs⌟ -∗
  mem_inj I' E.
Proof using Type.
  iIntros (-> Hls Hlt) "(%Hbij & %HE & Hin) Ht Hs %H".

  iAssert (⌜∀ lt', (ls, lt') ∉ I⌝)%I with "[Hin Hs]" as "%Hs".
  {
    iIntros (lt' Hej).
    iDestruct (big_sepS_delete _ _ _ Hej with "Hin") as "[Hcond H]".
    rewrite decide_False; last done.
    iDestruct "Hcond" as (vt' vs') "(_ & Ht' & Hs')".
    by iDestruct (src_points_to_unique with "Hs Hs'") as "%Hneq".
  }

  iAssert (⌜∀ ls', (ls', lt) ∉ I⌝)%I with "[Hin Ht]" as "%Ht".
  {
    iIntros (ls' Hej).
    iDestruct (big_sepS_delete _ _ _ Hej with "Hin") as "[Hcond H]".
    case_decide as He.
    - apply sdom_spec in He as [lt' Hlt'].
      assert (Heq: lt = lt').
      { eapply bij_set_functional.
        - by apply Hbij.
        - by apply Hej.
        - by apply HE.
      }
      subst lt. exfalso. apply Hlt. apply tdom_spec. by eexists.
    - iDestruct "Hcond" as (vt' vs') "(_ & Ht' & Hs')".
      by iDestruct (tgt_points_to_unique with "Ht Ht'") as "%Hneq".
  }

  iSplitR. { iPureIntro. by apply bij_set_extend. }
  iSplitR. { iPureIntro. intros ? ?. by apply elem_of_union_r, HE. }
  iApply big_sepS_union.
  { intros [] He%elem_of_singleton Hj. inv He. by apply (Ht ls). }
  iSplitR "Hin".
  - iApply big_sepS_singleton. rewrite decide_False; last done.
    iExists vt, vs. iFrame. iPureIntro.
    apply same_val_mono with I.
    + by apply union_subseteq_r.
    + done.
  - iApply (big_sepS_impl with "Hin").
    iModIntro. iIntros ([lt'' ls''] Hin).
    case_decide.
    + by iIntros "$".
    + iIntros "(%vt' & %vs' & %Hsame & Hcond)".
      iExists vt', vs'. iFrame.
      iPureIntro.
      apply same_val_mono with I.
      * by apply union_subseteq_r.
      * done.
Qed.

Lemma inj_insert I I' lt ls vt vs :
  I' = {[ (ls, lt) ]} ∪ I ->
  mem_inj I ∅ -∗
  lt →ₜ vt -∗
  ls →ₛ vs -∗
  ⌜same_val I vt vs⌟ -∗
  mem_inj I' ∅.
Proof using Type.
  intros. apply inj_insert_exploit; by set_solver.
Qed.

Lemma inj_exploit I E lt ls :
  related I lt ls ->
  ls ∉ sdom E ->
  mem_inj I E -∗
  ∃ E' vt vs,
    lt →ₜ vt ∗
    ls →ₛ vs ∗
    ⌜same_val I vt vs⌟ ∗
    ⌜E' = {[ (ls, lt) ]} ∪ E⌟ ∗
    mem_inj I E'.
Proof using Type.
  iIntros (Hrel HnE) "(%Hbij & %HE & Hin)".
  iDestruct (big_sepS_delete _ _ _ Hrel with "Hin") as "[Hpair Hin]".
  rewrite decide_False; last done.
  iDestruct "Hpair" as (vt vs) "(%Hsame & Ht & Hs)".
  iExists _, vt, vs. iFrame.
  iSplitR. { done. }
  iSplitR. { done. }
  iSplitR. { done. }
  iSplitR. { iPureIntro. intros p [->%elem_of_singleton | Hin]%elem_of_union; by auto. }
  iApply (big_sepS_delete _ _ _ Hrel).
  iSplitR.
  - rewrite decide_True; first done.
    apply sdom_spec. eexists.
    by apply elem_of_union_l, elem_of_singleton.
  - iApply (big_sepS_impl with "Hin").
    iModIntro.
    iIntros ([ls' lt'] Hneq).
    assert (ls ≠ ls') by (by eapply bij_set_diff_fst_neq).
    case_decide as He.
    + iIntros "_". rewrite decide_True; first done.
      apply sdom_spec in He  as [lt'' Hin].
      apply sdom_spec. exists lt''. by apply elem_of_union_r.
    + iIntros "(%vt' & %vs' & Hsame & Hcond)".
      rewrite decide_False; first iFrame.
      intros [lt'' Hin]%sdom_spec.
      apply elem_of_union in Hin as [Heq%elem_of_singleton | Hin ].
      * by inv Heq.
      * apply He, sdom_spec. by exists lt''.
Qed.

Lemma inj_release I E E' lt ls vt vs:
  (ls, lt) ∈ E ->
  E' = E ∖ {[ (ls, lt) ]} ->
  same_val I vt vs ->
  mem_inj I E -∗
  lt →ₜ vt -∗
  ls →ₛ vs -∗
  mem_inj I E'.
Proof using Type.
  iIntros (HE -> Hsame) "(%Hbij & %Hinj & Hin) Ht Hs".
  iSplitR. { done. }
  iSplitR.
  { iPureIntro. intros ? [Hin ?]%elem_of_difference. by apply Hinj, Hin. }
  assert (Hin: (ls, lt) ∈ I) by (now apply Hinj).
  iDestruct (big_sepS_delete _ _ _ Hin with "Hin") as "[H Hin]".
  iApply (big_sepS_delete _ _ _ Hin).
  iSplitL "Ht Hs".
  { rewrite decide_False.
    - iExists vt, vs. by iFrame.
    - intros [lt' [Hin' HnIn]%elem_of_difference]%sdom_spec.
      apply HnIn, elem_of_singleton. f_equal.
      by eapply bij_set_functional; eauto. }
  iApply (big_sepS_impl with "Hin").
  rewrite decide_True.
  - iDestruct "H" as "_".
    iModIntro.
    iIntros ([ls' lt'] Hin').
    assert (ls ≠ ls') by (by eapply bij_set_diff_fst_neq).
    case_decide as He.
    + iIntros "_".
      rewrite decide_True; first done.
      apply sdom_spec in He as [lt'' He].
      apply sdom_spec. exists lt''.
      apply elem_of_difference. split; first done.
      intros Hcontra%elem_of_singleton.
      inv Hcontra.
    + iIntros "(%vt' & %vs' & Hsame & H)".
      rewrite decide_False; first iFrame.
      intros Hcontra.
      apply He.
      apply sdom_spec in Hcontra as [y Hinc].
      apply elem_of_difference in Hinc as [].
      apply sdom_spec. by exists y.
  - apply sdom_spec. by eexists.
Qed.
