From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.FreeSim.
From RSL Require Import Simulations.Equiv.

Section FTest.
  Context {Λₜ Λₛ: lang}.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Abbreviation fsim := (fsim _ _ Pₜ Pₛ Φ).

  Definition coind_rule :=
    ∀ t s,
    (fsim true t true s -> fsim false t false s) ->
    fsim false t false s.

  CoInductive always_loop {Λ: lang} (P: prog Λ) (s: state Λ) : Prop :=
  | all_loop_do_step :
    can_progress P s ->
    (∀ s', P ⊨ s ->> s' -> always_loop P s') ->
    always_loop P s.

  Lemma ohnooo:
    ∀ t s,
    stuck Pₜ t ->
    always_loop Pₛ s ->
    coind_rule ->
    False.
  Proof using Type.
    intros t s Hstuck Hloop Hcoind.
    assert (Hfalse: ~fsim false t false s).
    {
      cut (∀ i j : bool, fsim j t i s -> j = false -> False).
      { intros HH Hsim. eapply HH; eassumption || reflexivity.  }
      unfold fsim. intros i j Hf.
      apply fsim_unroll in Hf.
      revert i j Hf.
      induction 1 as
        [ j t i s Hfinal
        | j t i s Hsstuck
        | j t i i' s s' Hs ? IHs
        | j t i s Hprogress IHt
        | j j' t i i' s Hprogress ? Hgfp ]; intros Hj.
      - destruct Hfinal as (? & ? & ? & ? & ?). mixin.
      - inv Hloop. mixin.
      - apply IHs.
        + assumption.
        + inv Hloop as [Hprogress Hloop']. now apply Hloop'.
        + assumption.
      - mixin.
      - subst. inv Hprogress.
    }
    assert (Htrue: ~fsim true t true s).
    {
      cut (∀ i j : bool, fsim j t i s -> j = true -> False).
      { intros HH Hsim. eapply HH; eassumption || reflexivity.  }
      unfold fsim. intros i j Hf.
      apply fsim_unroll in Hf.
      revert i j Hf.
      induction 1 as
        [ j t i s Hfinal
        | j t i s Hsstuck
        | j t i i' s s' Hs ? IHs
        | j t i s Hprogress IHt
        | j j' t i i' s Hltj Hlti Hgfp ]; intros Hj.
      - destruct Hfinal as (? & ? & ? & ? & ?). mixin.
      - inv Hloop. mixin.
      - apply IHs.
        + assumption.
        + inv Hloop as [Hprogress Hloop']. now apply Hloop'.
        + intros Hsim.
          apply Hfalse.
          eapply index_irrel with (J := WfBool) (I := WfBool) (i := false).
          * apply bool_not_isolated.
          * apply bool_not_isolated.
          * apply fsim_roll.
            eapply FSourceSteps; eassumption.
        + assumption.
      - mixin.
      - inv Hltj. inv Hlti. now apply Hfalse.
    }
    specialize (Hcoind t s). tauto.
  Qed.

  Definition strong_coind_rule :=
    ∀ (i j: bool) t s,
    ( (∀ i' j', i ⊏ i' -> j ⊏ j' -> fsim j' t i' s) ->
      fsim j t i s) ->
    fsim j t i s.

  Lemma weak_to_strong: coind_rule -> strong_coind_rule.
  Proof using Type.
    intros H i j t s IHs.
    eapply index_irrel with (i := false) (j := false);
     try apply bool_not_isolated.
    apply H.
    intros IH.
    eapply index_irrel with (i := i) (j := j);
     try apply bool_not_isolated.
    apply IHs.
    intros i' j' Hi Hj. inv Hi. now inv Hj.
  Qed.

  Lemma strong_to_weak: strong_coind_rule -> coind_rule.
  Proof using Type.
    intros H t s IHw.
    apply H.
    intros IHs.
    apply IHw.
    now apply IHs.
  Qed.

  Lemma strong_ohnooo:
    ∀ t s,
    stuck Pₜ t ->
    always_loop Pₛ s ->
    strong_coind_rule ->
    False.
  Proof using Type.
    intros.
    eapply ohnooo; try eassumption.
    now apply strong_to_weak.
  Qed.

End FTest.
