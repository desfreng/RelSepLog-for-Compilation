From RSL Require Import RelLogic Prelude.

From Coinduction Require Import all.

From RSL Require Import Simulations.FreeSim.
From RSL Require Import Simulations.FreeSimRules.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.SimRules.

From RSL Require Import Tactics.Memory.

Import RTLNotations.

Section TargetRulesDef.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation fsim := (fsim WfNat WfNat Pₜ Pₛ).

  Notation
    "'[' C ']' ρ '⊢' ft '@' pct  '<{' j ',' i '}=' fs '@' pcs '{{' Q '}}'" :=
    (sim Pₜ Pₛ C ρ ft pct j i fs pcs Q%rlogic)
      (at level 0, ft at level 0, fs at level 0, no associativity).

  Notation
    "'[' C ']' ρ '⊢' '{{' P '}}' ft '@' pct  '<{' j ',' i '}=' fs '@' pcs '{{' Q '}}'" :=
    (hoare Pₜ Pₛ C ρ P%rlogic ft pct j i fs pcs Q%rlogic)
      (at level 0, ft at level 0, fs at level 0, no associativity).

  Lemma target_nop C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ pc,
    fₜ@pcₜ is <<{ nop -> pc }>> ->
    [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pc <{1+j, i}= fₛ @ pcₛ {{ Q }} ->
    [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros pc Hpc H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    eapply FTargetSteps.
    - eexists. econstructor; eassumption.
    - intros t Hstep. inv Hstep.
      eexists. now apply H.
  Qed.

  Lemma target_op C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ pc dst op regs args v,
    fₜ@pcₜ is <<{ dst := @op regs -> pc }>> ->
    ρₜ @ regs ⇒ args ->
    eval_op op args = Some v ->
    [C] (⟦dst ⇐ v⟧ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pc <{1+j, i}= fₛ @ pcₛ {{ Q }} ->
    [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros pc dst op regs args v Hpc Hargs Hv H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep. simregs.
      eexists. now apply H.
  Qed.

  Lemma target_load C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ pc dst src addr v,
    fₜ@pcₜ is <<{ dst := !src -> pc }>> ->
    ρₜ @ src ⇒ addr ->
    [C] (⟦dst ⇐ v⟧ρₜ, ρₛ) ⊢ {{ addr →ₜ v ∗ P }} fₜ @ pc <{1+j, i}= fₛ @ pcₛ {{ Q }} ->
    [C] (ρₜ, ρₛ) ⊢ {{ addr →ₜ v ∗ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros pc dst src addr v Hpc Haddr H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    destruct Hpre as (mtAddr & msAddr & mtP & msP & ? & ? & ? & ? & Hm & HP).
    destruct Hm as ((l & Hl & Ht) & Hs).

    eapply FTargetSteps.
    - eexists. eapply exec_Iload; try eassumption.
      + subst. now simget.
      + reflexivity.
    - subst.
      intros t Hstep.
      inv Hstep. simregs. simget. subst.

      eexists. apply H; try solve_map_disjoint.
      eexists _, ∅, mtP, msP. repeat split; eauto.
      exists l. now split.
  Qed.

  Lemma target_store C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ pc dst src addr v old,
    fₜ@pcₜ is <<{ !dst := src -> pc }>> ->
    ρₜ @ dst ⇒ addr ->
    ρₜ @ src ⇒ v ->
    [C] (ρₜ, ρₛ) ⊢ {{ addr →ₜ v ∗ P }} fₜ @ pc <{1+j, i}= fₛ @ pcₛ {{ Q }} ->
    [C] (ρₜ, ρₛ) ⊢ {{ addr →ₜ old ∗ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros pc dst src addr v old Hpc Haddr Hv H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    destruct Hpre as (mtAddr & msAddr & mtP & msP & ? & ? & ? & ? & Hm & HP).
    destruct Hm as ((l & Hl & Ht) & Hs).

    eapply FTargetSteps.
    - eexists. eapply exec_Istore; try eassumption.
      subst.
      erewrite (set_at_some  _ _ _ _ _ Hl) by simget.
      rewrite !alter_union_right, !alter_union_left, alter_singleton by solve_map_disjoint.
      reflexivity.
    - intros t Hstep.
      inv Hstep.
      simregs.
      erewrite (set_at_some  _ _ _ _ _ Hl) in * by simget.
      rewrite !alter_union_right, !alter_union_left, alter_singleton
                in * by solve_map_disjoint.
      rewrite inj_some in *.

      subst. decompose_map_disjoint.
      eexists. apply H; try solve_map_disjoint.
      eexists _, ∅, mtP, msP. repeat split; eauto.
      + solve_map_disjoint.
      + solve_map_disjoint.
      + exists l. now split.
  Qed.

  Lemma target_if C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ pc_true pc_false reg v pc,
    fₜ@pcₜ is <<{ if reg then goto pc_true else goto pc_false }>> ->
    ρₜ @ reg ⇒ v ->
    (if (v =? 0)%Z then pc_true else pc_false) = pc ->
    [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pc <{1+j, i}= fₛ @ pcₛ {{ Q }} ->
    [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros pc_true pc_false reg v pc Hpc Hv Hnext_pc H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep. simregs.
      eexists. now apply H.
  Qed.

End TargetRulesDef.
