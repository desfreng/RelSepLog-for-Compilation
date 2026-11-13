From RSL Require Import Prelude.

From RSL.Language Require Export Language.
From RSL.Commons Require Export WfRel.

From Coinduction Require Import all.

Section CCAltSimDef.
  Context {Λt Λs: lang}.
  Context (W: WfRel) (Et: genv Λt) (Es: genv Λs) (ϕ: post Λt Λs).

  Variant ccalt_sim_step (gfp: W -> config Λt -> config Λs -> Prop)
    : W -> config Λt -> config Λs -> Prop :=
    | CCAltRelated : ∀ i t s s',
      Es ⊨ s ->>* s' ->
      both_final ϕ t s' ->
      ccalt_sim_step gfp i t s

    | CCAltStuck : ∀ i t s s',
      Es ⊨ s ->>* s' ->
      super_stuck Es s' ->
      ccalt_sim_step gfp i t s

    | CCAltTargetStep : ∀ i t s,
      can_progress Et t ->
      (∀ t', Et ⊨ t ->> t' -> ∃ i' s', i' ⊏ i ∧ Es ⊨ s ->>* s' ∧ gfp i' t' s') ->
      ccalt_sim_step gfp i t s

    | CCAltBothStep : ∀ i t s,
      can_progress Et t ->
      (∀ t', Et ⊨ t ->> t' -> ∃ i' s', Es ⊨ s ->>+ s' ∧ gfp i' t' s') ->
      ccalt_sim_step gfp i t s.

  Program Definition ccalt_sim_lfp : mon (element W -> config Λt -> config Λs -> Prop) :=
    {| body := ccalt_sim_step |}.
  Next Obligation.
    intros gfp gfp' Hgfp i t s Hsim.
    induction Hsim as [ i t s s' Hs Hfinal
                      | i t s s' Hs Hstuck
                      | i t s Hprog Hsim
                      | i t s Hprog Hsim ].
    - by econstructor.
    - by econstructor.
    - apply CCAltTargetStep. { done. }
      intros t' Ht.
      specialize (Hsim _ Ht) as (i' & s' & Hi & Hs & Hsim).
      exists i', s'. split_and!; auto.
      now apply Hgfp.
    - apply CCAltBothStep. { done. }
      intros t' Ht.
      specialize (Hsim _ Ht) as (i' & s' & Hs & Hsim).
      exists i', s'. split_and!; auto.
      now apply Hgfp.
  Qed.

  Lemma ccalt_sim_unroll i t s :
    gfp ccalt_sim_lfp i t s -> ccalt_sim_step (gfp ccalt_sim_lfp) i t s.
  Proof using Type. apply (gfp_fp ccalt_sim_lfp). Qed.

  Lemma nsim_roll i t s :
    ccalt_sim_step (gfp ccalt_sim_lfp) i t s -> gfp ccalt_sim_lfp i t s.
  Proof using Type. apply (gfp_fp ccalt_sim_lfp). Qed.

  Definition ccalt_sim  := gfp ccalt_sim_lfp.

  Lemma ccalt_sim_idx_mono (R: Chain ccalt_sim_lfp):
    ∀ i t s,
    (elem R) i t s ->
    ∀ i',
    i ⊑ i' ->
    (elem R) i' t s.
  Proof using Type.
    apply tower.
    { intros P Hp i t s Hinf i' Hi.
      intros Q Hq. eapply (Hp _ Hq); try eassumption.
      now apply Hinf.
    }
    clear R. intros R CIH i t s Hsim.
    induction Hsim as [ i t s s' Hs Hfinal
                      | i t s s' Hs Hstuck
                      | i t s Hprog Hsim
                      | i t s Hprog Hsim ].
    - by econstructor.
    - by econstructor.
    - intros i' Hi.
      apply CCAltTargetStep. { done. }
      intros t' Ht.
      specialize (Hsim _ Ht) as (i'' & s' & Hi' & Hs & Hsim).
      eexists _, s'.
      split; [| by split].
      by eapply lt_from_lt_le.
    - intros i' Hi.
      apply CCAltBothStep. { done. }
      intros t' Ht.
      specialize (Hsim _ Ht) as (i'' & s' & Hs & Hsim).
      by exists i'', s'.
  Qed.
End CCAltSimDef.
