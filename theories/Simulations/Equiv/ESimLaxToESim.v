From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.ExplicitSim.
From RSL Require Import Simulations.Equiv.ExplicitSimLax.

Section PROOF.
  Context {Λt Λs: lang}.
  Context (W: WfRel) (Pt: prog Λt) (Ps: prog Λs).
  Context (Φ: value Λt * memory -> value Λs * memory -> Prop).

  Definition Wnew : WfRel := WfLexProd W WfNat.

  Lemma esim_lax_to_esim_inv: ∀ n i t s s',
    Ps ⊨ s -{ n }> s' ->
    esim_lax W Pt Ps Φ i t s' ->
    esim Wnew Pt Ps Φ (ord_pair _ _ i n) t s.
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
      + destruct (pstep_to_nstep_l _ _ Hsteps) as (n & s' & Hstep & Hnstep).
        eapply ESourceSteps with (i' := ord_pair _ _ _ _).
        * eassumption.
        * by constructor.
        * eapply cih; eassumption.
      + apply ETargetSteps.
        { assumption. }
        intros t' Hstep. destruct (Ht _ Hstep) as (i' & Hlt & Hgfp).
        eexists (ord_pair _ _ _ 0). split.
        * constructor. done.
        * eapply cih; eassumption || constructor.
      + apply EBothSteps.
        { assumption. }
        intros t' Hstep.
        destruct (Hboth _ Hstep) as (i' & s'' & Hs & Hgfp).
        destruct (pstep_to_nstep_l _ _ Hs) as (n & s' & Hsteps & Hnstep).
        do 2 eexists. split.
        * eassumption.
        * eapply cih; eassumption || constructor.
    - intros i t s s' Hstep Hgfp.
      inv Hstep as [ | ? ? ? ? Hs Hnstep ].
      eapply ESourceSteps with (i' := ord_pair _ _ _ n).
      + eassumption.
      + right. simpl. lia.
      + eapply cih; eassumption.
  Qed.

  Lemma esim_lax_implies_esim: ∀ i t s,
    esim_lax W Pt Ps Φ i t s ->
    ∃ (R: WfRel) w, esim R Pt Ps Φ w t s.
  Proof using Type.
    intros i t s Hsim.
    exists Wnew, (ord_pair _ _ i 0).
    apply esim_lax_to_esim_inv with s.
    - constructor.
    - assumption.
  Qed.
End PROOF.
