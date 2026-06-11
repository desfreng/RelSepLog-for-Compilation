From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.FreeSim.
From RSL Require Import Simulations.Equiv.

Section FSimRules.
  Context {Λₜ Λₛ: lang}.
  Context (J I: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation fsim := (fsim J I Pₜ Pₛ).
  Abbreviation fsim_lfp := (fsim_lfp J I Pₜ Pₛ).

  Implicit Types (C: Chain fsim_lfp).

  Lemma fsim_in_chain Post:
    ∀ j t i s,
    (∀ C, fsim_lfp (elem C) Post j t i s) ->
    fsim Post j t i s.
  Proof using Type.
    intros j t i s Hr.
    unfold fsim.
    apply (gfp_prop).
    intros C.
    apply (b_chain C), Hr.
  Qed.

  Lemma final C Post:
    ∀ j t i s,
    both_final Post t s ->
    elem C Post j t i s.
  Proof using Type.
    apply tower.
    { intros P Hp j t i s H Q Hq. eapply Hp; now eauto. }
    intros C' CIH j t i s H. econstructor; now eauto.
  Qed.

  Lemma stuck C Post:
    ∀ j t i s,
    stuck Pₛ s ->
    elem C Post j t i s.
  Proof using Type.
    apply tower.
    { intros P Hp j t i s H Q Hq. eapply Hp; now eauto. }
    intros C' CIH j t i s H. econstructor; now eauto.
  Qed.

  Lemma source_step C Post:
    ∀ j t i i' s s',
    Pₛ ⊨ s ->> s' ->
    elem C Post j t i' s' ->
    elem C Post j t i s.
  Proof using Type.
    apply tower.
    { intros P Hp j t i i' s s' Hstep H Q Hq. eapply Hp; now eauto. }
    intros C' CIH j t i i' s s' Hstep H. econstructor; now eauto.
  Qed.

  Lemma target_step C Post:
    ∀ j t i s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ j', elem C Post j' t' i s) ->
    elem C Post j t i s.
  Proof using Type.
    apply tower.
    { intros P Hp j t i s Hprogesss H Q Hq.
      eapply Hp; eauto.
      intros t' Hstep. destruct (H _ Hstep) as [j' Hinf].
      exists j'. now auto. }
    intros C' CIH j t i s Hprogress Ht. econstructor; now eauto.
  Qed.

  Lemma progress_step C Post:
    ∀ j j' t i i' s,
    j' ⊏ j ->
    i' ⊏ i ->
    elem C Post j' t i' s ->
    elem C Post j t i s.
  Proof using Type.
    apply tower.
    { intros P Hp j j' t i i' s Ht Hs H Q Hq.
      eapply Hp; now eauto. }
    intros C' CIH j j' t i i' s Ht Hs H.
    eapply FProgress; try eassumption.
    now apply (b_chain C').
  Qed.

  Lemma coind_weak C Post:
    ∀ j t i s,
    (∀ C,
       (∀ j' i', j ⊏ j' -> i ⊏ i' -> fsim_lfp (elem C) Post j' t i' s) ->
       fsim_lfp (elem C) Post j t i s) ->
    elem C Post j t i s.
  Proof using Type.
    intros j t i s RIH.
    apply tower.
    { intros P Hp Q Hq. eapply Hp; now eauto. }
    intros C' CIH.
    apply RIH. intros j' i' Hj Hi.
    eapply FProgress; now eauto.
  Qed.

  Lemma coind_strong C Post P:
    (∀ C j t i s,
       (∀ j' t i' s,
          P Post j t i s ->
          j ⊏ j' ->
          i ⊏ i' ->
          fsim_lfp (elem C) Post j' t i' s) ->
       P Post j t i s ->
       fsim_lfp (elem C) Post j t i s) ->
    ∀ j t i s,
    P Post j t i s ->
    elem C Post j t i s.
  Proof using Type.
    intros RIH.
    apply tower.
    { intros Z Hz j t i s HP Q Hq. eapply Hz; now eauto. }
    intros C' CIH j t i s HP.
    apply RIH.
    - intros j' t' i' s' HP' Hj Hi.
      eapply FProgress; now eauto.
    - assumption.
  Qed.

  Lemma coind_weak_open Post:
    ∀ j t i s,
    (∀ R,
       (∀ j' i',
          j ⊏ j' ->
          i ⊏ i' ->
          fsim_lfp R Post j' t i' s) ->
       fsim_lfp R Post j t i s) ->
    fsim_lfp fsim Post j t i s.
  Proof using Type.
    intros j t i s RIH.
    apply fsim_unroll.
    coinduction C CIH.
    apply RIH. intros j' i' Hj Hi.
    eapply FProgress; now eauto.
  Qed.

  Lemma coind_strong_open Post P:
    (∀ R j t i s,
       (∀ j' t i' s,
          P Post j t i s ->
          j ⊏ j' ->
          i ⊏ i' ->
          fsim_lfp R Post j' t i' s) ->
       P Post j t i s ->
       fsim_lfp R Post j t i s) ->
    ∀ j t i s,
    P Post j t i s ->
    fsim_lfp fsim Post j t i s.
  Proof using Type.
    intros RIH j t i s HP.
    apply fsim_unroll.
    revert j t i s HP.
    coinduction C CIH.
    intros j t i s HP.
    apply RIH.
    - intros j' t' i' s' Hj Hi HP'.
      eapply FProgress; now eauto.
    - assumption.
  Qed.
End FSimRules.
