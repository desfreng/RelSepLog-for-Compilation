From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations Require Export Explicit ExplicitLax.

Section PROOF.
  Context {Λt Λs: lang}.
  Context (W: WfRel) (Et: genv Λt) (Es: genv Λs).
  Context (ϕ: post Λt Λs).

  Lemma esim_lax_implies_esim_inv: ∀ n i t s s',
    Es ⊨ s ->>_(n) s' ->
    esim_lax W Et Es ϕ i t s' ->
    esim _ Et Es ϕ (ord_pair i n) t s.
  Proof using Type.
    unfold esim.
    coinduction C cih.
    intros n.
    induction n as [ | n IH ].
    - intros i t s s' Hstep Hsim. inv Hstep.
      apply esim_lax_unroll in Hsim.
      induction Hsim as
        [ i t s Hfin
        | i t s Hstuck
        | i i' t s s'' Hsteps Hlt Hgfp
        | i t s Hprogress Ht
        | i t s Hprogress Hboth ].
      + now constructor.
      + now constructor.
      + destruct (psteps_to_nsteps_l _ _ _ Hsteps) as (n & s' & Hstep & Hnstep).
        eapply ESourceSteps with (i' := ord_pair _ _).
        * eassumption.
        * by constructor.
        * eapply cih; eassumption.
      + apply ETargetSteps.
        { assumption. }
        intros t' Hstep. destruct (Ht _ Hstep) as (i' & Hlt & Hgfp).
        eexists (ord_pair _ 0). split.
        * constructor. done.
        * eapply cih; eassumption || constructor.
      + apply EBothSteps.
        { assumption. }
        intros t' Hstep.
        destruct (Hboth _ Hstep) as (i' & s'' & Hs & Hgfp).
        destruct (psteps_to_nsteps_l _ _ _ Hs) as (n & s' & Hsteps & Hnstep).
        do 2 eexists. split.
        * eassumption.
        * eapply cih; eassumption || constructor.
    - intros i t s s' Hstep Hgfp.
      inv Hstep as [ | ? ? ? ? Hs Hnstep ].
      eapply ESourceSteps with (i' := ord_pair _ n).
      + eassumption.
      + right. simpl. lia.
      + eapply cih; eassumption.
  Qed.
End PROOF.
