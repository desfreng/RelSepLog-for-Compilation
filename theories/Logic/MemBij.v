From RSL Require Import Prelude.

From RSL.Commons Require Export BijSet.
From RSL.Logic Require Export PointsTo.

Definition related (j: gset (loc * loc)) (lt ls: loc) :=
  (lt, ls) ∈ j.

Definition same_val (j: gset (loc * loc)) := val_eq (related j).

Lemma same_val_mono j j' vt vs :
  j ⊆ j' ->
  same_val j vt vs ->
  same_val j' vt vs.
Proof using Type.
  destruct vt as [], vs as []; simpl; auto.
  unfold related. by auto.
Qed.

Definition mem_inj (j : gset (loc * loc)) : rProp :=
  (
    ⌜bij_set j⌝ ∗
    [∗ set] '(lt, ls) ∈ j,
      ∃ vt vs,
        lt →ₜ vt ∗
        ls →ₛ vs ∗
        ⌜same_val j vt vs⌝
  )%I.

Lemma inj_empty : ⊢ mem_inj ∅.
Proof using Type.
  unfold mem_inj.
  iSplit.
  - iPureIntro. by apply bij_set_empty.
  - by iApply big_sepS_empty.
Qed.

Lemma inj_insert j lt ls vt vs :
  mem_inj j -∗
  lt →ₜ vt -∗
  ls →ₛ vs -∗
  ⌜same_val j vt vs⌝ -∗
  mem_inj ({[ (lt, ls) ]} ∪ j).
Proof using Type.
  unfold mem_inj.
  iIntros "[Hbij Hin] Ht Hs %H".
  iAssert (⌜∀ lt, (lt, ls) ∉ j⌝)%I with "[-Ht]" as "%Ht".
  {
    iIntros (lt' He).
    iDestruct (big_sepS_elem_of _ _ _ He with "Hin")
      as (vt' vs') "(_ & Hs' & _)".
    by iDestruct (src_points_to_unique with "Hs Hs'") as "%Hneq".
  }
  iAssert (⌜∀ ls, (lt, ls) ∉ j⌝)%I with "[-Hs]" as "%Hs".
  {
    iIntros (ls' He).
    iDestruct (big_sepS_elem_of _ _ _ He with "Hin")
      as (vt' vs') "(Ht' & _ & _)".
    by iDestruct (tgt_points_to_unique with "Ht Ht'") as "%Hneq".
  }
  iSplitL "Hbij". { iRevert "Hbij". iPureIntro. intro Hbij. by apply bij_set_extend. }
  iApply big_sepS_union.
  { intros [] He%elem_of_singleton. inv He. by apply Ht. }
  iSplitR "Hin".
  - iApply big_sepS_singleton.
    iFrame. iPureIntro.
    apply same_val_mono with j.
    + by apply union_subseteq_r.
    + easy.
  - iApply (big_sepS_impl with "Hin"). clear.
    iIntros "!>".
    iIntros ([lt' ls'] Hin) "(%vt' & %vs' & Ht & Hs & %Hsame)".
    iExists vt', vs'. iFrame.
    iPureIntro.
    apply same_val_mono with j.
    + by apply union_subseteq_r.
    + easy.
Qed.
