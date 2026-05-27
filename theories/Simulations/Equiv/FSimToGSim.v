From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL Require Import Commons.OrdTree.

From RSL Require Import Simulations.Commons.
From RSL Require Import Simulations.FreeSim.

From RSL Require Import Simulations.Equiv.GSim.

Section PROOF.
  Context {Λₜ Λₛ: lang}.
  Context (Wₜ Wₛ: WfRel).
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Definition StatePair := (state Λₜ * state Λₛ)%type.

  Lemma fsim_implies_gsim: ∀ iₜ t iₛ s,
    fsim Wₜ Wₛ Pₜ Pₛ Φ iₜ t iₛ s ->
    ∃ wₜ wₛ,
      gsim Wₜ Wₛ (WfOrdTree StatePair) Pₜ Pₛ Φ iₜ wₜ t iₛ wₛ s.
  Proof using Type.
    intros iₜ t iₛ s Hsim.
    apply fsim_unroll in Hsim.
    induction Hsim as [ iₜ t iₛ s Hfinal
                      | iₜ t iₛ s Hstuck
                      | iₜ t iₛ iₛ' s s' Hs Hsim IHs
                      | iₜ t iₛ s Hprogress IHt
                      | iₜ iₜ' t iₛ iₛ' s Hprogress1 Hprogress2 Hasim ].
    - exists (ord_tree_base StatePair), (ord_tree_base StatePair).
      now econstructor.
    - exists (ord_tree_base StatePair), (ord_tree_base StatePair).
      now econstructor.
    - destruct IHs as (wₜ' & wₛ' & Hinv).
      exists wₜ', (ord_tree_cons StatePair (fun _ => wₛ')).
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
                   ∃ (iₜ: Wₜ) wₛ,
                     gsim _ _ _ Pₜ Pₛ Φ iₜ o t' iₛ wₛ s).

      assert (Hord: ∀ a, P a -> ∃ o, R a o).
      { intros [t' s'] [Heq Hstep]. subst s'.
        destruct (IHt t' Hstep) as (iₜ' & ? & wₜ' & wₛ' & Hsim').
        exists wₜ'. split; [reflexivity|]. split; [assumption|].
        exists iₜ'. exists wₛ'. exact Hsim'. }
      destruct (ord_tree_join StatePair P R Hord) as [wₜ Hjoin1].

      pose (R2 := fun (a: StatePair) (o: ord_tree StatePair) =>
                    let (t', s') := a in
                    s' = s ∧
                    Pₜ ⊨ t ->> t' ∧
                    ∃ (iₜ': Wₜ) wₜ',
                       wₜ' ⊏ wₜ ∧
                      gsim _ _ _ Pₜ Pₛ Φ iₜ' wₜ' t' iₛ o s).
      assert (Hord2: ∀ a, P a -> ∃ o, R2 a o).
      { intros [t' s'] [Heq Hstep]. subst s'.
        destruct (Hjoin1 (t', s)) as [wₜ' [Hrw Hlt]].
        { split; [reflexivity|assumption]. }
        destruct Hrw as (_ & Hstep' & iₜ' & wₛ' & Hsim').
        exists wₛ'. split; [reflexivity|]. split; [assumption|].
        exists iₜ'.
        exists wₜ'. split; [exact Hlt|exact Hsim']. }
      destruct (ord_tree_join StatePair P R2 Hord2) as [wₛ Hjoin2].
      clear Hord R Hjoin1.

      exists wₜ, wₛ.
      eapply GTargetSteps.
      + eassumption.
      + intros t' Hstep.
        destruct (Hjoin2 (t', s)) as (wₛ' & Hrw & Hlt).
        { split; reflexivity || assumption. }
        destruct Hrw as (_ & Hstep' & iₜ' & wₜ' &  Hlt_wₜ & Hsim').
        exists iₜ'. exists wₜ'. split.
        * assumption.
        * apply gsim_weaken_s with wₛ'.
          { assumption. }
          now constructor.
    - exists (ord_tree_base StatePair), (ord_tree_base StatePair).
      econstructor; eassumption.
  Qed.
End PROOF.
