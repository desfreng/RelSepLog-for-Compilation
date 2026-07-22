From RSL Require Import Prelude.

From RSL.Logic Require Export PointsTo.
From RSL.Commons Require Export BijSet.

From RSL.Commons Require Import RegisterBank.

Implicit Types (I E : gset (loc * loc)) (lt ls : loc).

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

Definition mem_inj I E : rProp :=
  (
    ⌜bij_set I⌟ ∗
    ⌜E ⊆ I⌟ ∗
    [∗ set] '(ls, lt) ∈ I,
        if (decide (ls ∈ dom E))
        then emp
        else
          ∃ vt vs,
            ⌜same_val I vt vs⌟ ∗ lt →ₜ vt ∗ ls →ₛ vs
  )%I.

Lemma inj_empty : ⊢ mem_inj ∅ ∅.
Proof using Type.
  unfold mem_inj.
  iSplit.
  { iPureIntro. by apply bij_set_empty. }
  iSplit.
  { easy. }
  { by iApply big_sepS_empty. }
Qed.

Lemma inj_insert_exploit I E lt ls vt vs :
  ls ∉ dom E ->
  lt ∉ codom E ->
  mem_inj I E -∗
  lt →ₜ vt -∗
  ls →ₛ vs -∗
  ⌜same_val I vt vs⌟ -∗
  mem_inj ({[ (ls, lt) ]} ∪ I) E.
Proof using Type.
  iIntros (Hls Hlt) "(%Hbij & %HE & Hin) Ht Hs %H".

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
    - apply dom_spec in He as [lt' Hlt'].
      assert (Heq: lt = lt').
      { eapply bij_set_functional.
        - by apply Hbij.
        - by apply Hej.
        - by apply HE.
      }
      subst lt. exfalso. apply Hlt. apply codom_spec. by eexists.
    - iDestruct "Hcond" as (vt' vs') "(_ & Ht' & Hs')".
      by iDestruct (tgt_points_to_unique with "Ht Ht'") as "%Hneq".
  }

  iSplitR.
  { iPureIntro. by apply bij_set_extend. }
  iSplitR.
  { iPureIntro. transitivity I; auto. by apply union_subseteq_r. }
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

Lemma inj_insert I lt ls vt vs :
  mem_inj I ∅ -∗
  lt →ₜ vt -∗
  ls →ₛ vs -∗
  ⌜same_val I vt vs⌟ -∗
  mem_inj ({[ (ls, lt) ]} ∪ I) ∅.
Proof using Type. by apply inj_insert_exploit. Qed.

Lemma inj_exploit I E lt ls :
  related I lt ls ->
  ls ∉ dom E ->
  mem_inj I E -∗
  ∃ vt vs,
    lt →ₜ vt ∗
    ls →ₛ vs ∗
    ⌜same_val I vt vs⌟ ∗
    mem_inj I ({[ (ls, lt) ]} ∪ E).
Proof using Type.
  iIntros (Hrel HnE) "(%Hbij & %HE & Hin)".
  iDestruct (big_sepS_delete _ _ _ Hrel with "Hin") as "[Hpair Hin]".
  rewrite decide_False; last done.
  iDestruct "Hpair" as (vt vs) "(%Hsame & Ht & Hs)".
  iExists vt, vs. iFrame.
  iSplitR. { done. }

  iSplitR. { done. }
  iSplitR.
  { iPureIntro. apply union_subseteq. split.
    - by apply elem_of_subseteq_singleton.
    - easy.
  }
  iApply (big_sepS_delete _ _ _ Hrel).
  iSplitR.
  - rewrite decide_True; first done.
    apply dom_spec. eexists.
    by apply elem_of_union_l, elem_of_singleton.
  - iApply (big_sepS_impl with "Hin").
    iModIntro.
    iIntros ([ls' lt'] Hneq).
    assert (ls ≠ ls') by (by eapply bij_set_diff_fst_neq).
    case_decide as He.
    + iIntros "_". rewrite decide_True; first done.
      apply dom_union. by right.
    + iIntros "(%vt' & %vs' & Hsame & Hcond)".
      rewrite decide_False; first iFrame.
      intros [->%dom_singleton | HinE]%dom_union; contradiction.
Qed.

Lemma inj_release I E lt ls vt vs:
  (ls, lt) ∈ E ->
  same_val I vt vs ->
  mem_inj I E -∗
  lt →ₜ vt -∗
  ls →ₛ vs -∗
  mem_inj I (E ∖ {[ (ls, lt) ]}).
Proof using Type.
  iIntros (HE Hsame) "(%Hbij & %Hinj & Hin) Ht Hs".
  iSplitR. { done. }
  iSplitR.
  { iPureIntro. by apply subseteq_difference_l. }
  assert (Hin: (ls, lt) ∈ I) by (now apply Hinj).
  iDestruct (big_sepS_delete _ _ _ Hin with "Hin") as "[H Hin]".
  iApply (big_sepS_delete _ _ _ Hin).
  iSplitL "Ht Hs".
  { rewrite decide_False.
    - iExists vt, vs. by iFrame.
    - intros [lt' [Hin' HnIn]%elem_of_difference]%dom_spec.
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
      apply dom_spec in He as [lt'' He].
      apply dom_spec. exists lt''.
      apply elem_of_difference. split; first done.
      intros Hcontra%elem_of_singleton.
      inv Hcontra.
    + iIntros "(%vt' & %vs' & Hsame & H)".
      rewrite decide_False; first iFrame.
      intros Hcontra.
      apply He.
      apply dom_spec in Hcontra as [y Hinc].
      apply elem_of_difference in Hinc as [].
      apply dom_spec. by exists y.
  - apply dom_spec. by eexists.
Qed.
