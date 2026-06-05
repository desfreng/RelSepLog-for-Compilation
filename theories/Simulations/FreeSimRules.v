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

  Lemma fsim_in_chain Φ:
    ∀ j t i s,
    (∀ R : Chain fsim_lfp, fsim_lfp (elem R) Φ j t i s) ->
    fsim Φ j t i s.
  Proof using Type.
    intros j t i s Hr.
    unfold fsim.
    apply (gfp_prop).
    intros C.
    apply (b_chain C), Hr.
  Qed.

  Lemma final (C: Chain fsim_lfp) Φ:
    ∀ j t i s,
    both_final Φ t s ->
    fsim_lfp (elem C) Φ j t i s.
  Proof using Type.
    apply tower.
    { intros P Hp j t i s H Q Hq. eapply Hp; now eauto. }
    intros C' CIH j t i s H. econstructor; now eauto.
  Qed.

  Lemma stuck (C: Chain fsim_lfp) Φ:
    ∀ j t i s,
    stuck Pₛ s ->
    fsim_lfp (elem C) Φ j t i s.
  Proof using Type.
    apply tower.
    { intros P Hp j t i s H Q Hq. eapply Hp; now eauto. }
    intros C' CIH j t i s H. econstructor; now eauto.
  Qed.

  Lemma source_step (C: Chain fsim_lfp) Φ:
    ∀ j t i i' s s',
    Pₛ ⊨ s ->> s' ->
    fsim_lfp (elem C) Φ j t i' s' ->
    fsim_lfp (elem C) Φ j t i s.
  Proof using Type.
    apply tower.
    { intros P Hp j t i i' s s' Hstep H Q Hq. eapply Hp; now eauto. }
    intros C' CIH j t i i' s s' Hstep H. econstructor; now eauto.
  Qed.

  Lemma target_step (C: Chain fsim_lfp) Φ:
    ∀ j t i s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ j', fsim_lfp (elem C) Φ j' t' i s) ->
    fsim_lfp (elem C) Φ j t i s.
  Proof using Type.
    apply tower.
    { intros P Hp j t i s Hprogesss H Q Hq.
      eapply Hp; eauto.
      intros t' Hstep. destruct (H _ Hstep) as [j' Hinf].
      exists j'. now auto. }
    intros C' CIH j t i s Hprogress Ht. econstructor; now eauto.
  Qed.

  Lemma progress_step (C: Chain fsim_lfp) Φ:
    ∀ j j' t i i' s,
    j' ⊏ j ->
    i' ⊏ i ->
    fsim_lfp (elem C) Φ j' t i' s ->
    fsim_lfp (elem C) Φ j t i s.
  Proof using Type.
    apply tower.
    { intros P Hp j j' t i i' s Ht Hs H Q Hq.
      eapply Hp; now eauto. }
    intros C' CIH j j' t i i' s Ht Hs H.
    eapply FProgress; try eassumption.
    now apply (b_chain C').
  Qed.

  Lemma coind (C: Chain fsim_lfp) Φ:
    ∀ t s,
    (∀ C': Chain fsim_lfp,
       ∀ j i,
       (∀ i' j', i ⊏ i' -> j ⊏ j' -> fsim_lfp (elem C') Φ j' t i' s) ->
       fsim_lfp (elem C') Φ j t i s) ->
    ∀ j i, fsim_lfp (elem C) Φ j t i s.
  Proof using Type.
    intros t s RIH.
    apply tower.
    { intros P Hp j i Q Hq. eapply Hp; now eauto. }
    intros C' CIH j i.
    eapply fsim_lfp'_mono with (x := elem C').
    - intros Ψ i' l' j' r' Hsim. assumption.
    - eapply RIH.
      intros i' j' Hi Hj.
      eapply FProgress; now eauto.
  Qed.
End FSimRules.
