From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations Require Export ExplicitAlt ExplicitLax.

Section PROOF.
  Context {Λt Λs: lang}.
  Context (J I: WfRel).
  Context (Et: genv Λt) (Es: genv Λs).
  Context (ϕ: post Λt Λs).

  Lemma ealt_sim_implies_esim_lax: ∀ b t a s,
    ealt_sim J I Et Es ϕ b t a s ->
    esim_lax (WfWithBot (WfLexProd J I)) Et Es ϕ (Some (ord_pair b a)) t s.
  Proof using Type.
    unfold esim_lax.
    coinduction R cih.
    intros b t a s Hsim.
    apply ealt_sim_unroll in Hsim.
    induction Hsim as [ b t a s Hfinal
                      | b t a s Hstuck
                      | b b' t a a' s s' Hstep _ Hsim
                      | b t a s Hprogress Ht
                      | b t a s Hprogress Hboth].
    - now constructor.
    - now constructor.
    - assert (Hrtc: Es ⊨ s ->>+ s').
      { econstructor; eassumption || reflexivity. }
      clear Hstep. revert b' s' Hrtc Hsim.
      induction a' as [a' IHw] using (well_founded_ind wf).
      intros b' s' Hrtc Hsim.
      apply ealt_sim_unroll in Hsim.
      induction Hsim as [ b' t a' s' Hfinal
                        | b' t a' s' Hstuck
                        | b' b'' t a' a'' s' s'' Hstep Hlt Hsim
                        | b' t a' s' Hprogress Ht
                        | b' t a' s' Hprogress Hboth].
      + eapply ELaxSourceSteps.
        * eassumption.
        * now constructor.
        * apply (@b_chain _ _ _ R). now constructor.
      + eapply ELaxSourceSteps.
        * eassumption.
        * now constructor.
        * apply (@b_chain _ _ _ R). now constructor.
      + eapply IHw.
        * eassumption.
        * eapply psteps_r; eassumption.
        * eassumption.
      + apply ELaxBothSteps.
        { assumption. }
        intros t' Htstep.
        destruct (Ht _ Htstep) as (b'' & a'' & Hlt & Hsim).
        exists (Some (ord_pair b'' a'')), s'. split.
        * assumption.
        * apply cih. eassumption.
      + apply ELaxBothSteps.
        { assumption. }
        intros t' Htstep.
        destruct (Hboth _ Htstep) as (b'' & a'' & s'' & Hsteps & Hsim).
        exists (Some (ord_pair b'' a'')), s''. split.
        * eapply psteps_r; eassumption.
        * apply cih. eassumption.
    - apply ELaxTargetSteps.
      { assumption. }
      intros t' Hstep.
      destruct (Ht _ Hstep) as (b' & a' & Hlt & Hgfp).
      eexists (Some (ord_pair b' _)). split.
      + do 2 constructor. done.
      + apply cih. eassumption.
    - apply ELaxBothSteps.
      { assumption. }
      intros t' Hstep.
      edestruct (Hboth _ Hstep) as (b' & a' & s' & Hs & Hsim).
      exists (Some (ord_pair b' a')), s'. split.
      + econstructor; eassumption || reflexivity.
      + apply cih. assumption.
  Qed.
End PROOF.
