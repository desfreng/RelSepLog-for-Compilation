From RSL Require Import Prelude.

From RSL.Commons Require Export BijSet.
From RSL.Logic Require Export PointsTo.

Definition related (j: gset (loc * loc)) (lt ls: loc) :=
  (ls, lt) ∈ j.

Definition same_val (j: gset (loc * loc)) := val_eq (related j).

Lemma same_val_mono j j' vt vs :
  j ⊆ j' ->
  same_val j vt vs ->
  same_val j' vt vs.
Proof using Type.
  destruct vt as [], vs as []; simpl; auto.
  unfold related. by auto.
Qed.

Definition in_inj (j : gset (loc * loc)) (E: gmap loc loc) :=
  ∀ ls lt, E !! ls = Some lt -> (ls, lt) ∈ j.

Lemma in_inj_mono j j' E : j ⊆ j' -> in_inj j E -> in_inj j' E.
Proof using Type.
  by intros Hincl Hinj lt ls H; auto.
Qed.

Lemma in_inj_extend j E lt ls :
  related j lt ls ->
  in_inj j E ->
  in_inj j (<[ls:=lt]> E).
Proof using Type.
  intros Hrel Hinj ls' lt'.
  rewrite lookup_insert.
  case_decide as He.
  - intros H. by inv H.
  - intros HeE. by apply Hinj.
Qed.

Lemma in_inj_remove j E ls :
  in_inj j E ->
  in_inj j (delete ls E).
Proof using Type.
  intros Hinj ls' lt'.
  rewrite lookup_delete.
  case_decide as He.
  - intros H. by inv H.
  - intros HeE. by apply Hinj.
Qed.

Definition mem_inj (j : gset (loc * loc)) (E: gmap loc loc) : rProp :=
  (
    ⌜bij_set j⌟ ∗
    ⌜in_inj j E⌟ ∗
    [∗ set] '(ls, lt) ∈ j,
      ∃ vt vs,
        ⌜same_val j vt vs⌟ ∗
        if (E !! ls)
        then emp
        else lt →ₜ vt ∗ ls →ₛ vs
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

Lemma inj_insert_exploit j E lt ls vt vs :
  E !! ls = None ->
  (∀ ls' lt', E !! ls' = Some lt' -> lt' ≠ lt) ->
  mem_inj j E -∗
  lt →ₜ vt -∗
  ls →ₛ vs -∗
  ⌜same_val j vt vs⌟ -∗
  mem_inj ({[ (ls, lt) ]} ∪ j) E.
Proof using Type.
  iIntros (Hls Hlt) "(%Hbij & %HE & Hin) Ht Hs %H".

  iAssert (⌜∀ lt', (ls, lt') ∉ j⌝)%I with "[Hin Hs]" as "%Hs".
  {
    iIntros (lt' Hej).
    iDestruct (big_sepS_delete _ _ _ Hej with "Hin") as "[Hcond H]".
    rewrite Hls.
    iDestruct "Hcond" as (vt' vs') "(_ & Ht' & Hs')".
    by iDestruct (src_points_to_unique with "Hs Hs'") as "%Hneq".
  }

  iAssert (⌜∀ ls', (ls', lt) ∉ j⌝)%I with "[Hin Ht]" as "%Ht".
  {
    iIntros (ls' Hej).
    iDestruct (big_sepS_delete _ _ _ Hej with "Hin") as "[Hcond H]".
    destruct (E !! ls') as [lt'| ] eqn:HeE.
    - assert (lt = lt'). { by eapply bij_set_functional; eauto. }
      subst lt'. exfalso. by eapply Hlt.
    - iDestruct "Hcond" as (vt' vs') "(_ & Ht' & Hs')".
      by iDestruct (tgt_points_to_unique with "Ht Ht'") as "%Hneq".
  }

  iSplitR.
  { iPureIntro. by apply bij_set_extend. }
  iSplitR.
  { iPureIntro. apply in_inj_mono with j; auto. by apply union_subseteq_r. }
  iApply big_sepS_union.
  { intros [] He%elem_of_singleton Hj. inv He. by apply (Ht ls). }
  iSplitR "Hin".
  - iApply big_sepS_singleton. rewrite Hls.
    iExists vt, vs. iFrame. iPureIntro.
    apply same_val_mono with j; auto.
    by apply union_subseteq_r.
  - iApply (big_sepS_impl with "Hin").
    iModIntro. iIntros ([lt'' ls''] Hin) "(%vt' & %vs' & %Hsame & Hcond)".
    iExists vt', vs'. iFrame.
    iPureIntro.
    apply same_val_mono with j; auto.
    by apply union_subseteq_r.
Qed.

Lemma inj_insert j lt ls vt vs :
  mem_inj j ∅ -∗
  lt →ₜ vt -∗
  ls →ₛ vs -∗
  ⌜same_val j vt vs⌟ -∗
  mem_inj ({[ (ls, lt) ]} ∪ j) ∅.
Proof using Type. by apply inj_insert_exploit. Qed.

Lemma inj_exploit j E lt ls :
  related j lt ls ->
  E !! ls = None ->
  mem_inj j E -∗
  ∃ vt vs,
    lt →ₜ vt ∗
    ls →ₛ vs ∗
    ⌜same_val j vt vs⌟ ∗
    mem_inj j (<[ls := lt]>E).
Proof using Type.
  iIntros (Hrel HnE) "(%Hbij & %HE & Hin)".
  iDestruct (big_sepS_delete _ _ _ Hrel with "Hin") as "[Hpair Hin]".
  iDestruct "Hpair" as (vt vs) "[%Hsame Hcond]".
  rewrite HnE.
  iDestruct "Hcond" as "[Ht Hs]".
  iExists vt, vs. iFrame.
  iSplitR. { done. }

  iSplitR. { done. }
  iSplitR. { iPureIntro. by apply in_inj_extend. }

  iApply (big_sepS_delete _ _ _ Hrel).
  iSplitR.
  - iExists vt, vs. by rewrite lookup_insert decide_True.
  - iApply (big_sepS_impl with "Hin").
    iModIntro.
    iIntros ([ls' lt'] Hneq).
    iIntros "(%vt' & %vs' & Hsame & Hcond)".
    iExists vt', vs'. iFrame.
    assert (ls ≠ ls') by (by eapply bij_set_diff_fst_neq).
    now rewrite lookup_insert_ne.
Qed.

Lemma inj_release j E lt ls vt vs:
  E !! ls = Some lt ->
  same_val j vt vs ->
  mem_inj j E -∗
  lt →ₜ vt -∗
  ls →ₛ vs -∗
  mem_inj j (delete ls E).
Proof using Type.
  iIntros (HE Hsame) "(%Hbij & %Hinj & Hin) Ht Hs".
  iSplitR. { done. }
  iSplitR. { iPureIntro. by apply in_inj_remove. }
  assert (Hin: (ls, lt) ∈ j) by (now apply Hinj).
  iDestruct (big_sepS_delete _ _ _ Hin with "Hin") as "[H Hin]".
  rewrite HE.
  iDestruct "H" as (vt' vs' Hsame') "_".
  iApply (big_sepS_delete _ _ _ Hin).
  iSplitL "Ht Hs".
  - iExists vt, vs. rewrite lookup_delete_eq. by iFrame.
  - iApply (big_sepS_impl with "Hin"). clear vt' vs' Hsame'.
    iModIntro.
    iIntros ([ls' lt'] Hin') "(%vt' & %vs' & Hsame & H)".
    iExists vt', vs'. iFrame.
    assert (ls ≠ ls') by (by eapply bij_set_diff_fst_neq).
    now rewrite lookup_delete_ne.
Qed.
