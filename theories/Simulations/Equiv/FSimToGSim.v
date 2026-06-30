From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Commons.OrdTree.

From RSL Require Import Simulations.FreeSim.
From RSL Require Import Simulations.Equiv.GSim.

Section PROOF.
  Context {Λₜ Λₛ: lang}.
  Context (J I: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Definition StatePair := (state Λₜ * state Λₛ)%type.

  Lemma fsim_implies_gsim: ∀ j t i s,
    fsim J I Pₜ Pₛ Φ t j i s ->
    ∃ b a,
      gsim J I (WfOrdTree StatePair) Pₜ Pₛ Φ j b t i a s.
  Proof using Type.
    intros t j i s Hsim.
    apply fsim_unroll in Hsim.
    induction Hsim as [ t j i s Hfinal
                      | t j i s Hstuck
                      | t j i i' s s' Hs Hsim IHs
                      | t j i s Hprogress IHt
                      | t j j' i i' s Hprogress1 Hprogress2 Hasim ].
    - exists (ord_tree_base StatePair), (ord_tree_base StatePair).
      now econstructor.
    - exists (ord_tree_base StatePair), (ord_tree_base StatePair).
      now econstructor.
    - destruct IHs as (b' & a' & Hinv).
      exists b', (ord_tree_cons StatePair (fun _ => a')).
      eapply GSourceSteps.
      + eassumption.
      + constructor. apply ord_tree_lt_intro with (a := (t, s')).
      + eassumption.
    - pose (P := fun a: StatePair =>
                   let (t', s') := a in
                   s' = s ∧ Pₜ ⊨ t ->> t').

      pose (R := fun (a: StatePair) (o: ord_tree StatePair) =>
                   let (t', s') := a in
                   s' = s ∧ Pₜ ⊨ t ->> t' ∧
                   ∃ (j: J) a,
                     gsim _ _ _ Pₜ Pₛ Φ j o t' i a s).

      assert (Hord: ∀ a, P a -> ∃ o, R a o).
      { intros [t' s'] [Heq Hstep]. subst s'.
        destruct (IHt t' Hstep) as (j' & ? & b' & a' & Hsim').
        exists b'. split; [reflexivity|]. split; [assumption|].
        exists j'. exists a'. exact Hsim'. }
      destruct (ord_tree_join StatePair P R Hord) as [b Hjoin1].

      pose (R2 := fun (a: StatePair) (o: ord_tree StatePair) =>
                    let (t', s') := a in
                    s' = s ∧
                    Pₜ ⊨ t ->> t' ∧
                    ∃ (j': J) b',
                       b' ⊏ b ∧
                      gsim _ _ _ Pₜ Pₛ Φ j' b' t' i o s).
      assert (Hord2: ∀ a, P a -> ∃ o, R2 a o).
      { intros [t' s'] [Heq Hstep]. subst s'.
        destruct (Hjoin1 (t', s)) as [b' [Hrw Hlt]].
        { split; [reflexivity|assumption]. }
        destruct Hrw as (_ & Hstep' & j' & a' & Hsim').
        exists a'. split; [reflexivity|]. split; [assumption|].
        exists j'.
        exists b'. split; [exact Hlt|exact Hsim']. }
      destruct (ord_tree_join StatePair P R2 Hord2) as [a Hjoin2].
      clear Hord R Hjoin1.

      exists b, a.
      eapply GTargetSteps.
      + eassumption.
      + intros t' Hstep.
        destruct (Hjoin2 (t', s)) as (a' & Hrw & Hlt).
        { split; reflexivity || assumption. }
        destruct Hrw as (_ & Hstep' & j' & b' &  Hlt_b & Hsim').
        exists j'. exists b'. split.
        * assumption.
        * apply gsim_weaken_s with a'.
          { assumption. }
          now constructor.
    - exists (ord_tree_base StatePair), (ord_tree_base StatePair).
      econstructor; eassumption.
  Qed.
End PROOF.
