From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations Require Export CompCertAlt ExplicitLax.

Section PROOF.
  Context {Λt Λs: lang}.
  Context (W: WfRel) (Et: genv Λt) (Es: genv Λs).
  Context (ϕ: post Λt Λs).

  Lemma ccalt_implies_explicit_lax i t s:
    ccalt_sim W Et Es ϕ i t s ->
    esim_lax _ Et Es ϕ (ord_pair i true) t s.
  Proof using Type.
    revert i t s.
    unfold esim_lax.
    coinduction R CIH.
    intros i t s Hsim%ccalt_sim_unroll.
    destruct Hsim as [ i t s s' Hs Hfinal
                     | i t s s' Hs Hstuck
                     | i t s Hprog Hsim
                     | i t s Hprog Hsim ].
    - apply steps_inv_psteps in Hs as [-> | Hs].
      + by apply ELaxRelated.
      + eapply ELaxSourceSteps with (i' := ord_pair i false).
        * done.
        * by constructor.
        * apply (b_chain R). by apply ELaxRelated.
    - apply steps_inv_psteps in Hs as [-> | Hs].
      + by apply ELaxSourceStuck.
      + eapply ELaxSourceSteps with (i' := ord_pair i false).
        * done.
        * by constructor.
        * apply (b_chain R). by apply ELaxSourceStuck.
    - apply ELaxTargetSteps. { done. }
      intros t' Ht.
      specialize (Hsim _ Ht) as (i' & s' & Hi & Hs & Hsim).
      apply steps_inv_psteps in Hs as [-> | Hs].
      + exists (ord_pair i' true).
        split; first by constructor.
        by apply CIH.
      + exists (ord_pair i false).
        split; first by constructor.
        apply (b_chain R).
        eapply ELaxSourceSteps with (i' := ord_pair i' true).
        * done.
        * by constructor.
        * by apply CIH.
    - apply ELaxBothSteps. { done. }
      intros t' Ht.
      specialize (Hsim _ Ht) as (i' & s' & Hs & Hsim).
      exists (ord_pair i' true), s'.
      split. { done. }
      by apply CIH.
  Qed.

  Lemma explicit_lax_ccalt_inv i t s:
    ∀ s',
    Es ⊨ s ->>* s' ->
    esim_lax W Et Es ϕ i t s' ->
    ccalt_sim W Et Es ϕ i t s.
  Proof using Type.
    revert i t s.
    unfold ccalt_sim.
    coinduction R CIH.
    intros i.
    induction i as [i IHi] using (well_founded_induction wf).
    intros t s s' Hs Hsim%esim_lax_unroll.
    induction Hsim as [ i t s' Hfinal
                      | i t s' Hstuck
                      | i i' t s' s'' Hs' Hi Hsim
                      | i t s' Hprog Hsim
                      | i t s' Hprog Hsim ].
    - by eapply CCAltRelated.
    - by eapply CCAltStuck.
    - {
        apply esim_lax_unroll in Hsim.
        induction Hsim as [ i' t s'' Hfinal
                          | i' t s'' Hstuck
                          | i' i'' t s'' s''' Hs'' Hi' Hsim
                          | i' t s'' Hprog Hsim
                          | i' t s'' Hprog Hsim ].
        - eapply CCAltRelated.
          + etransitivity. { done. } by apply psteps_to_steps.
          + done.
        - eapply CCAltStuck.
          + etransitivity. { done. } by apply psteps_to_steps.
          + done.
        - eapply ccalt_sim_idx_mono.
          + eapply IHi.
            * done.
            * done.
            * eapply esim_lax_roll, ELaxSourceSteps.
              { by etransitivity. }
              { done. }
              { done. }
          + by left.
        - apply CCAltBothStep. { done. }
          intros t' Ht.
          specialize (Hsim _ Ht) as (i'' & _ & Hsim).
          exists i'', s''.
          split.
          + by eapply psteps_steps_l.
          + by eapply CIH.
        - apply CCAltBothStep. { done. }
          intros t' Ht.
          specialize (Hsim _ Ht) as (i'' & s''' & Hs'' & Hsim).
          exists i'', s'''.
          split.
          + eapply psteps_steps_l. { done. }
            by etransitivity.
          + by eapply CIH.
      }
    - apply CCAltTargetStep. { done. }
      intros t' Ht.
      specialize (Hsim _ Ht) as (i' & Hi & Hsim).
      exists i', s'.
      split_and!.
      + done.
      + done.
      + by eapply CIH.
    - apply CCAltBothStep. { done. }
      intros t' Ht.
      specialize (Hsim _ Ht) as (i'' & s'' & Hs' & Hsim).
      exists i'', s''.
      split.
      + by eapply psteps_steps_l.
      + by eapply CIH.
  Qed.

  Lemma explicit_lax_cimplies_calt i t s:
    esim_lax W Et Es ϕ i t s ->
    ccalt_sim W Et Es ϕ i t s.
  Proof using Type.
    by apply explicit_lax_ccalt_inv.
  Qed.

End PROOF.
