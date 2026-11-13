From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations Require Export CompCert CompCertAlt.

Section PROOF.
  Context {Λt Λs: lang}.
  Context (W: WfRel) (Et: genv Λt) (Es: genv Λs).
  Context (ϕ: post Λt Λs).

  Lemma ccalt_sim_implies_ccsim i t s:
    ccalt_sim W Et Es ϕ i t s -> ccsim W Et Es ϕ i t s.
  Proof using Type.
    revert i t s.
    unfold ccsim.
    coinduction R CIH.
    intros i t s Hsim%ccalt_sim_unroll.
    induction Hsim as [ i t s s' Hs Hfinal
                      | i t s s' Hs Hstuck
                      | i t s Hprog Hsim
                      | i t s Hprog Hsim ].
    - by eapply CCRelated.
    - by eapply CCStuck.
    - apply CCProgress. { done. }
      intros t' Ht.
      specialize (Hsim _ Ht) as (i' & s' & Hi & Hs & Hsim).
      left. exists i', s'. split_and!; by auto.
    - apply CCProgress. { done. }
      intros t' Ht.
      specialize (Hsim _ Ht) as (i' & s' & Hs & Hsim).
      right. exists i', s'. split_and!; by auto.
  Qed.


  (** [t] can move and [s] is strictly behind a state [s'] that simulates [t]. *)
  Definition lag t s : Prop :=
    can_progress Et t ∧
    exists s' i, Es ⊨ s ->>+ s' ∧ ccsim W Et Es ϕ i t s'.

  (** The pair (t, s) is finishing: either it is final and related or s can be stuck *)
  Definition finishing t s : Prop :=
    (∃ s', Es ⊨ s ->>* s' ∧ both_final ϕ t s') ∨
      (∃ s', Es ⊨ s ->>* s' ∧ super_stuck Es s').

  Lemma ccsim_nsim_inv t s :
    ∀ k,
    ((∃ i, (ord_pair i true) = k /\ ccsim W Et Es ϕ i t s) ∨ lag t s ∨ finishing t s) ->
    ccalt_sim _ Et Es ϕ k t s.
  Proof using Type.
    revert t s.
    unfold ccalt_sim.
    coinduction R CIH.
    intros t s k [(i & <- & Hsim%ccsim_unroll) | [Hlag | Hfin]].
    {
      destruct Hsim as [ i t s s' Hs Hfinal
                       | i t s s' Hs Hstuck
                       | i t s Hprog Hsim ].
      - by eapply CCAltRelated.
      - by eapply CCAltStuck.
      - apply CCAltTargetStep. { done. }
        intros t' Ht.
        specialize (Hsim _ Ht)
          as [ (i' & s' & Hi & Hs & Hsim) | (i' & s' & Hs & Hsim) ].
        + exists (ord_pair i' true), s'. split_and!.
          * by constructor.
          * done.
          * apply CIH. left. by exists i'.
        + apply ccsim_unroll in Hsim.
          destruct Hsim as [ i' t' s' s'' Hs' Hfinal
                           | i' t' s' s'' Hs' Hstuck
                           | i' t' s' Hprog' Hsim ].
          * exists (ord_pair i false), s'. split_and!.
            { by constructor. }
            { by apply psteps_to_steps. }
            apply CIH.
            do 2 right. left.
            by eauto.
          * exists (ord_pair i false), s'. split_and!.
            { by constructor. }
            { by apply psteps_to_steps. }
            apply CIH.
            do 3 right. by eauto.
          * exists (ord_pair i false), s. split_and!.
            { by constructor. }
            { done. }
            apply CIH. right. left.
            split. { done. }
            exists s', i'. split. { done. }
            by apply ccsim_roll, CCProgress.
    }
    {
      destruct Hlag as (Hprog & s' & i' & Hs & Hsim%ccsim_unroll).
      destruct Hsim as [ i t s' s'' Hs' Hfinal
                       | i t s' s'' Hs' Hstuck
                       | i t s' Hprog' Hsim ].
      - eapply CCAltRelated.
        + etransitivity; last done. by apply psteps_to_steps.
        + done.
      - eapply CCAltStuck.
        + etransitivity; last done. by apply psteps_to_steps.
        + done.
      - apply CCAltBothStep. { done. }
        intros t' Ht.
        specialize (Hsim _ Ht)
          as [ (i' & s'' & Hi & Hs' & Hsim) | (i' & s'' & Hs' & Hsim) ].
        + exists (ord_pair i' true), s''. split.
          * by eapply psteps_steps_r.
          * apply CIH. left. by exists i'.
        + exists (ord_pair i' true), s''. split.
          * by etransitivity.
          * apply CIH. left. by exists i'.
    }
    {
      destruct Hfin as [ (s' & Hs & Hfin) | (s' & Hs & Hstuck) ].
      - by eapply CCAltRelated.
      - by eapply CCAltStuck.
    }
  Qed.

  Lemma ccsim_implies_ccalt_sim i t s:
    ccsim W Et Es ϕ i t s -> ccalt_sim _ Et Es ϕ (ord_pair i true) t s.
  Proof using Type.
    intros Hsim.
    apply ccsim_nsim_inv.
    left. by exists i.
  Qed.

End PROOF.
