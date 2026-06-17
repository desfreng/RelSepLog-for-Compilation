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

Section SourceRulesDef.
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

  Lemma source_nop C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ pc,
    fₛ@pcₛ is <<{ nop -> pc }>> ->
    [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, 1+i}= fₛ @ pc {{ Q }} ->
    [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros pc Hpc H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    eapply FSourceSteps.
    - econstructor; eassumption.
    - now apply H.
  Qed.

  Lemma source_op C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ pc dst op regs args,
    fₛ@pcₛ is <<{ dst := @op regs -> pc }>> ->
    ρₛ @ regs ⇒ args ->
    (∀ v, eval_op op args = Some v ->
     [C] (ρₜ, ⟦dst ⇐ v⟧ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, 1+i}= fₛ @ pc {{ Q }}) ->
    [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros pc dst op regs args Hpc Hargs H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    destruct (eval_op op args) as [v|] eqn:Hv.
    - eapply FSourceSteps.
      + econstructor; eassumption || reflexivity.
      + now eapply H.
    - apply FSourceStuck.
      split.
      { reflexivity. }
      intros Hprog. apply can_progress_must_step in Hprog.
      destruct Hprog as [? Hprog].
      inv Hprog. simregs.
  Qed.

  Lemma source_load C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ pc dst src addr v,
    fₛ@pcₛ is <<{ dst := !src -> pc }>> ->
    ρₛ @ src ⇒ addr ->
    [C] (ρₜ, ⟦dst ⇐ v⟧ρₛ) ⊢ {{ addr →ₛ v ∗ P }} fₜ @ pcₜ <{j, 1+i}= fₛ @ pc {{ Q }} ->
    [C] (ρₜ, ρₛ) ⊢ {{ addr →ₛ v ∗ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros pc dst src addr v Hpc Haddr H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    destruct Hpre as (mtAddr & msAddr & mtP & msP & ? & ? & ? & ? & Hm & HP).
    destruct Hm as (Ht & (l & Hl & Hs)).

    eapply FSourceSteps.
    - eapply exec_Iload with (v := v); try eassumption.
      + subst. now simget.
      + reflexivity.
    - apply H; auto.
      eexists mtAddr, msAddr, mtP, msP.
      repeat split; auto.
      eexists. split; eassumption.
  Qed.

  Lemma source_store C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ pc dst src addr v old,
    fₛ@pcₛ is <<{ !dst := src -> pc }>> ->
    ρₛ @ dst ⇒ addr ->
    ρₛ @ src ⇒ v ->
    [C] (ρₜ, ρₛ) ⊢ {{ addr →ₛ v ∗ P }} fₜ @ pcₜ <{j, 1+i}= fₛ @ pc {{ Q }} ->
    [C] (ρₜ, ρₛ) ⊢ {{ addr →ₛ old ∗ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros pc dst src addr v old Hpc Haddr Hv H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    destruct Hpre as (mtAddr & msAddr & mtP & msP & ? & ? & ? & ? & Hm & HP).
    destruct Hm as (Ht & (l & Hl & Hs)).

    eapply FSourceSteps.
    - eapply exec_Istore; try eassumption.
      subst. erewrite (set_at_some  _ _ _ _ _ Hl) by now simget.
      rewrite !alter_union_right by solve_map_disjoint.
      rewrite !alter_union_left by solve_map_disjoint.
      rewrite !alter_singleton.
      reflexivity.
    - subst. apply H; try solve_map_disjoint.
      eexists ∅, _, mtP, msP. repeat split; eauto.
      + solve_map_disjoint.
      + exists l. now split.
  Qed.

  Lemma source_if C ρₜ ρₛ P fₜ pcₜ j i fₛ pcₛ Q :
    ∀ pc_true pc_false reg v pc,
    fₛ@pcₛ is <<{ if reg then goto pc_true else goto pc_false }>> ->
    ρₛ @ reg ⇒ v ->
    (if (v =? 0)%Z then pc_true else pc_false) = pc ->
    [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, 1+i}= fₛ @ pc {{ Q }} ->
    [C] (ρₜ, ρₛ) ⊢ {{ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Q }}.
  Proof using Type.
    intros pc_true pc_false reg v pc Hpc Hv Hnext_pc H.
    intros ? ? Hemp Ψ mtPre msPre ? ? Hpre mtPost msPost ? ? Hpost.

    eapply FSourceSteps.
    - econstructor; eassumption || reflexivity.
    - subst. now apply H.
  Qed.

End SourceRulesDef.
