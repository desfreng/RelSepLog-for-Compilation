From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.Commons.
From RSL Require Import Simulations.Equiv.ExplicitSimLax.
From RSL Require Import Simulations.Equiv.EAltSim.

Section PROOF.
  Context {Λₜ Λₛ: lang}.
  Context (Wₜ Wₛ: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Lemma ealt_sim_implies_esim_lax: ∀ wₜ t wₛ s,
    ealt_sim Wₜ Wₛ Pₜ Pₛ Φ wₜ t wₛ s ->
    ∃ W i, esim_lax W Pₜ Pₛ Φ i t s.
  Proof.
    intros wₜ t wₛ s Hsim.
    exists (WfWithBot (WfLexProd Wₜ Wₛ)), (Some (wₜ, wₛ)).
    revert wₜ t wₛ s Hsim.
    unfold esim_lax.
    coinduction R cih.
    intros wₜ t wₛ s Hsim.
    apply ealt_sim_unroll in Hsim.
    induction Hsim as [ wₜ t wₛ s Hfinal
                      | wₜ t wₛ s Hstuck
                      | wₜ wₜ' t wₛ wₛ' s s' Hstep Hlt Hsim
                      | wₜ t wₛ s Hprogress Ht
                      | wₜ t wₛ s Hprogress Hboth].
    - now constructor.
    - now constructor.
    - assert (Hrtc: Pₛ ⊨ s ->>+ s').
      { econstructor. eassumption. reflexivity. }
      clear Hstep.
      revert wₜ' s' Hrtc Hsim.
      induction wₛ' as [wₛ' IHwₛ'] using (well_founded_ind wf).
      intros wₜ' s' Hrtc Hsim.
      apply ealt_sim_unroll in Hsim.
      inv Hsim.
      + eapply ELaxSourceSteps.
        * eassumption.
        * now constructor.
        * apply (@b_chain _ _ _ R).
          now constructor.
      + eapply ELaxSourceSteps.
        * eassumption.
        * now constructor.
        * apply (@b_chain _ _ _ R).
          now constructor.
      + (* EAltSourceSteps *)
        eapply IHwₛ'.
        * eassumption.
        * etransitivity; eassumption.
        * eapply pstep_r; eassumption.
        * eassumption.
      + (* EAltTargetSteps *)
        (* The target finally stepped. We can emit EBothSteps directly from the original state s *)
        eapply ELaxBothSteps.
        * eassumption.
        * intros t' Htstep.
          destruct (H0 _ Htstep) as (wₜ'' & wₛ'' & Hlt_wₜ & Hsim_next).
          exists (Some (wₜ'', wₛ'')), s'.
          split; try apply cih; eassumption.
      + (* EAltBothSteps *)
        eapply ELaxBothSteps.
        * eassumption.
        * intros t' Htstep.
          destruct (H0 _ Htstep) as (wₜ'' & wₛ'' & s'' & Hstep_s'' & Hsim_next).
          exists (Some (wₜ'', wₛ'')), s''.
          split.
          -- eapply pstep_r; eassumption.
          -- apply cih; eassumption.
    - apply ELaxTargetSteps.
      { assumption. }
      intros t' Hstep.
      destruct (Ht _ Hstep) as (wₜ' & wₛ' & Hlt & Hgfp).
      eexists. split.
      2: {
        apply cih.
        eassumption.
      }
      constructor. now left.
    - apply ELaxBothSteps.
      { assumption. }
      intros t' Hstep.
      edestruct (Hboth _ Hstep) as (wₜ' & wₛ' & s' & Hs & Hsim).
      exists (Some (wₜ', wₛ')), s'.
      split.
      + econstructor; eassumption || reflexivity.
      + apply cih. assumption.
  Qed.
End PROOF.
