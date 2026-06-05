From RSL Require Import Prelude RelLogic.

From Coinduction Require Import all.

From RSL Require Import Simulations.FreeSim.
From RSL Require Import Simulations.FreeSimRules.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Notations.

Import RTLNotations.

Section Rules.
  Let Λₜ : lang := rtl_lang.
  Let Λₛ : lang := rtl_lang.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ).

  Abbreviation fsim := (fsim WfNat WfNat Pₜ Pₛ).
  Abbreviation fsim_lfp := (fsim_lfp WfNat WfNat Pₜ Pₛ).
  Abbreviation post := (val -> val -> rlogic).

  Implicit Types C : Chain fsim_lfp.

  Definition sim C Γ Φ fₜ pcₜ j i fₛ pcₛ : rlogic :=
    let Φ : value Λₜ -> value Λₛ -> Prop :=
      fun '(vₜ, mₜ) '(vₛ, mₛ) => Φ vₜ vₛ mₜ mₛ
    in
    let '(ρₜ, ρₛ) := Γ in
    fun mₜ mₛ =>
      fsim_lfp (elem C) Φ
        j ([], State fₜ pcₜ ρₜ, mₜ)
        i ([], State fₛ pcₛ ρₛ, mₛ).

  Notation
    "C '|' Γ '⊢' ft '@' pct  '<{' j ',' i '}=' fs '@' pcs '{{' Φ '}}'" :=
    (sim C Γ Φ%rlogic ft pct j i fs pcs)
      (at level 1, ft at level 0, fs at level 0, no associativity).

  Definition hoare C Γ P fₜ pcₜ j i fₛ pcₛ (Q: post) : Prop :=
    ⊨ ∀ Φ,
      P -*
      (∀ vₜ vₛ, Q vₜ vₛ -* Φ vₜ vₛ) -*
      sim C Γ Φ fₜ pcₜ j i fₛ pcₛ.

  Notation
    "C '|' Γ '⊢' '{{' P '}}' ft '@' pct  '<{' j ',' i '}=' fs '@' pcs '{{' Q '}}'" :=
    (hoare C Γ P%rlogic ft pct j i fs pcs Q%rlogic)
      (at level 1, ft at level 0, fs at level 0, no associativity).

  Lemma both_ret C Γ (Φ: post)  fₜ pcₜ j i fₛ pcₛ :
    ∀ rₜ vₜ rₛ vₛ,
    fₜ@pcₜ is <<{ ret rₜ }>> ->
    fₛ@pcₛ is <<{ ret rₛ }>> ->
    Γ @ rₜ ⇒ₜ vₜ ->
    Γ @ rₛ ⇒ₛ vₛ ->
    C | Γ ⊢ {{ Φ vₜ vₛ }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros rt vt rs vs Hpct Hpcs Ht Hs.
    intros Ψ mt1 ms1 ? ? Hpre mt2 ms2 ? ? Hpost.

    simp. decompose_map_disjoint.
    destruct Γ as [ρₜ ρₛ].
    unfold rbank_assert_t, rbank_assert_t_single in Ht.
    unfold rbank_assert_s, rbank_assert_s_single in Hs.

    eapply FSourceSteps with (i' := 0).
    { eapply exec_Iret; eassumption. }

    eapply FTargetSteps.
    { eexists; eapply exec_Iret; eassumption. }

    intros t' Hstep. inv Hstep. exists 0.

    eapply FRelated.

    do 2 eexists; repeat split. simpl.

    rewrite (map_empty_union mt1).
    rewrite (map_empty_union ms1).

    erewrite (map_union_comm mt1 mt2) by eauto.
    erewrite (map_union_comm ms1 ms2) by eauto.
    apply Hpost.
    - solve_map_disjoint.
    - solve_map_disjoint.
    - apply Hpre.
  Qed.

  Lemma source_nop C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ pc,
    fₛ@pcₛ is <<{ nop -> pc }>> ->
    C | Γ ⊢ {{ ⌜⌝ }} fₜ @ pcₜ <{j, 1+i}= fₛ @ pc {{ Φ }} ->
    C | Γ ⊢ {{ ⌜⌝ }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros pc Hpc H.
    intros Ψ mt1 ms1 ? ? Hpre mt2 ms2 ? ? Hpost.

    simp.
    destruct Γ as [ρₜ ρₛ].

    eapply FSourceSteps.
    - econstructor; eassumption.
    - now apply H.
  Qed.

  Lemma target_nop C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ pc,
    fₜ@pcₜ is <<{ nop -> pc }>> ->
    C | Γ ⊢ {{ ⌜⌝ }} fₜ @ pc <{1+j, i}= fₛ @ pcₛ {{ Φ }} ->
    C | Γ ⊢ {{ ⌜⌝ }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros pc Hpc H.
    intros Ψ mt1 ms1 ? ? Hpre mt2 ms2 ? ? Hpost.

    simp.
    destruct Γ as [ρₜ ρₛ].

    eapply FTargetSteps.
    - eexists. econstructor; eassumption.
    - intros t Hstep. inv Hstep.
      eexists. now apply H.
  Qed.

  Lemma source_op C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst op regs args v,
    fₛ@pcₛ is <<{ dst := @op regs -> pc }>> ->
    eval_op op args = Some v ->
    Γ @ regs ⇒ₛ args ->
    C | ⟦ dst ⇐ₛ v ⟧Γ ⊢ {{ ⌜⌝ }} fₜ @ pcₜ <{j, 1+i}= fₛ @ pc {{ Φ }} ->
    C | Γ ⊢ {{ ⌜⌝ }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros pc dst op regs args v Hpc Hv Hargs H.
    intros Ψ mt1 ms1 ? ? Hpre mt2 ms2 ? ? Hpost.

    simp.
    destruct Γ as [ρₜ ρₛ].

    eapply FSourceSteps.
    - econstructor; eassumption || reflexivity.
    - now eapply H.
  Qed.

  Lemma target_op C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst op regs args v,
    fₜ@pcₜ is <<{ dst := @op regs -> pc }>> ->
    eval_op op args = Some v ->
    Γ @ regs ⇒ₜ args ->
    C | ⟦ dst ⇐ₜ v ⟧Γ ⊢ {{ ⌜⌝ }} fₜ @ pc <{1+j, i}= fₛ @ pcₛ {{ Φ }} ->
    C | Γ ⊢ {{ ⌜⌝ }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros pc dst op regs args v Hpc Hv Hargs H.
    intros Ψ mt1 ms1 ? ? Hpre mt2 ms2 ? ? Hpost.

    simp.
    destruct Γ as [ρₜ ρₛ].
    unfold rbank_assert_t, rbank_assert_t_list in Hargs.

    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep.
      eexists. now apply H.
  Qed.

  Lemma source_load C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst src addr v,
    fₛ@pcₛ is <<{ dst := !src -> pc }>> ->
    Γ @ src ⇒ₛ addr ->
    C | ⟦ dst ⇐ₛ v ⟧Γ ⊢ {{ addr →ₛ v }} fₜ @ pcₜ <{j, 1+i}= fₛ @ pc {{ Φ }} ->
    C | Γ ⊢ {{ addr →ₛ v }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros pc dst src addr v Hpc Haddr H.
    intros Ψ mt1 ms1 ? ? Hpre mt2 ms2 ? ? Hpost.

    simp.
    destruct Γ as [ρₜ ρₛ].
    apply get_at_unfold in Hpre. destruct Hpre as (loc & Hloc & Hget).

    eapply FSourceSteps.
    - eapply exec_Iload; try eassumption.
      + unfold get_at. rewrite Hloc. simpl_map. reflexivity.
      + reflexivity.
    - apply H; auto.
      unfold get_at. now rewrite Hloc.
  Qed.

  Lemma target_load C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst src addr v,
    fₜ@pcₜ is <<{ dst := !src -> pc }>> ->
    Γ @ src ⇒ₜ addr ->
    C | ⟦ dst ⇐ₜ v ⟧Γ ⊢ {{ addr →ₜ v }} fₜ @ pc <{1+j, i}= fₛ @ pcₛ {{ Φ }} ->
    C | Γ ⊢ {{ addr →ₜ v }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros pc dst src addr v Hpc Haddr H.
    intros Ψ mt1 ms1 ? ? Hpre mt2 ms2 ? ? Hpost.

    destruct Γ as [ρₜ ρₛ].
    unfold rbank_assert_t, rbank_assert_t_single in Haddr.
    apply get_at_unfold in Hpre.
    destruct Hpre as (loc & Hloc & Hmem).

    eapply FTargetSteps.
    - eexists. eapply exec_Iload; try eassumption.
      + unfold get_at. rewrite Hloc. simpl_map. reflexivity.
      + reflexivity.
    - intros t Hstep.
      inv Hstep as [ | | | ? ? ? ? ? ? ? ? ? ? ? ? ? Hget | | | | | ].
      unfold get_at in Hget. rewrite Hloc in Hget.
      simpl_map. inv Hget.
      eexists. eapply H; auto. simp.
      unfold get_at. now rewrite Hloc.
  Qed.

  Lemma source_store C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst src addr v old,
    fₛ@pcₛ is <<{ !dst := src -> pc }>> ->
    Γ @ dst ⇒ₛ addr ->
    Γ @ src ⇒ₛ v ->
    C | Γ ⊢ {{ addr →ₛ v }} fₜ @ pcₜ <{j, 1+i}= fₛ @ pc {{ Φ }} ->
    C | Γ ⊢ {{ addr →ₛ old }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros pc dst src addr v old Hpc Haddr Hv H.
    intros Ψ mt1 ms1 ? ? Hpre mt2 ms2 ? ? Hpost.

    simp.
    destruct Γ as [ρₜ ρₛ].
    apply get_at_unfold in Hpre. destruct Hpre as (l & Hloc & Hmem).

    eapply FSourceSteps.
    - eapply exec_Istore; try eassumption.
      unfold set_at, update_at. rewrite Hloc.
      simpl_map.
      rewrite (insert_union_l _ ms2).
      rewrite (insert_union_r ∅ ms1).
      + reflexivity.
      + eapply map_disjoint_Some_l; eassumption.
    - eapply H; auto.
      + apply map_disjoint_insert_l. split; now eauto.
      + unfold get_at. rewrite Hloc.
        now rewrite (lookup_insert_eq ms1).
      + decompose_map_disjoint.
        apply map_disjoint_union_r. split; auto.
        * solve_map_disjoint.
        * apply map_disjoint_insert_r. split; eauto.
          eapply map_disjoint_Some_r; eassumption.
  Qed.

  Lemma target_store C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ pc dst src addr v old,
    fₜ@pcₜ is <<{ !dst := src -> pc }>> ->
    Γ @ dst ⇒ₜ addr ->
    Γ @ src ⇒ₜ v ->
    C | Γ ⊢ {{ addr →ₜ v }} fₜ @ pc <{1+j, i}= fₛ @ pcₛ {{ Φ }} ->
    C | Γ ⊢ {{ addr →ₜ old }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros pc dst src addr v old Hpc Haddr Hv H.
    intros Ψ mt1 ms1 ? ? Hpre mt2 ms2 ? ? Hpost.

    destruct Γ as [ρₜ ρₛ].
    unfold rbank_assert_t, rbank_assert_t_single in Haddr, Hv.
    apply get_at_unfold in Hpre. destruct Hpre as (l & Hloc & Hmem).

    eapply FTargetSteps.
    - eexists. eapply exec_Istore; try eassumption.
      unfold set_at, update_at. rewrite Hloc.
      simpl_map. reflexivity.
    - intros t Hstep.
      inv Hstep as [ | | | | ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hm | | | | ].
      unfold set_at, update_at in Hm. rewrite Hloc in Hm.
      simpl_map.
      rewrite (insert_union_l _ mt2) in Hm.
      rewrite (insert_union_r ∅ mt1) in Hm by solve_map_disjoint.
      inv Hm.

      eexists. simp. apply H; auto.
      + apply map_disjoint_insert_l. split; now auto.
      + unfold get_at. rewrite Hloc.
        now rewrite (lookup_insert_eq mt1).
      + decompose_map_disjoint.
        apply map_disjoint_union_r. split; auto.
        * solve_map_disjoint.
        * apply map_disjoint_insert_r. split; eauto.
          eapply map_disjoint_Some_r; eassumption.
  Qed.

  Lemma source_if C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ pc_true pc_false reg v pc,
    fₛ@pcₛ is <<{ if reg then goto pc_true else goto pc_false }>> ->
    Γ @ reg ⇒ₛ v ->
    (if (v =? 0)%Z then pc_true else pc_false) = pc ->
    C | Γ ⊢ {{ ⌜⌝ }} fₜ @ pcₜ <{j, 1+i}= fₛ @ pc {{ Φ }} ->
    C | Γ ⊢ {{ ⌜⌝ }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros pc_true pc_false reg v pc Hpc Hv Hnext_pc H.
    intros Ψ ? ? ? ? Hpre ? ? ? ? Hpost. simp.

    destruct Γ as [ρₜ ρₛ].
    unfold rbank_assert_s, rbank_assert_s_single in Hv.

    eapply FSourceSteps.
    - econstructor; eassumption || reflexivity.
    - subst. now apply H.
  Qed.

  Lemma target_if C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ pc_true pc_false reg v pc,
    fₜ@pcₜ is <<{ if reg then goto pc_true else goto pc_false }>> ->
    Γ @ reg ⇒ₜ v ->
    (if (v =? 0)%Z then pc_true else pc_false) = pc ->
    C | Γ ⊢ {{ ⌜⌝ }} fₜ @ pc <{j, i}= fₛ @ pcₛ {{ Φ }} ->
    C | Γ ⊢ {{ ⌜⌝ }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros pc_true pc_false reg v pc Hpc Hv Hnext_pc H.
    intros Ψ ? ? ? ? Hpre ? ? ? ? Hpost. simp.

    destruct Γ as [ρₜ ρₛ].
    unfold rbank_assert_t, rbank_assert_t_single in Hv.

    eapply FTargetSteps.
    - eexists. econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep.
      eexists. now apply H.
  Qed.

  Lemma frame C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ P Q,
    C | Γ ⊢ {{ Q }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ fun vₜ vₛ => Φ vₜ vₛ }} ->
    C | Γ ⊢ {{ P ∗ Q }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ fun vₜ vₛ => P ∗ Φ vₜ vₛ }}.
  Proof using Type.
    intros P Q H.
    intros Ψ mt2 ms2 ? ? Hpre mt3 ms3 ? ? Hpost.
    decompose_map_disjoint.

    destruct Hpre as (mtP & mtQ & msP & msQ & ? & ? & ? & ? & Hp & Hq).

    unfold hoare in H. simp.

    rewrite (map_empty_union mt2).
    rewrite (map_empty_union ms2).

    subst. decompose_map_disjoint.

    rewrite (map_union_comm mtP mtQ) by auto.
    rewrite (map_union_comm msP msQ) by auto.

    rewrite <- (map_union_assoc mtQ mtP mt3).
    rewrite <- (map_union_assoc msQ msP ms3).

    rewrite <- (map_empty_union (mtQ ∪ (mtP ∪ mt3))).
    rewrite <- (map_empty_union (msQ ∪ (msP ∪ ms3))).

    rewrite ! (map_union_assoc ∅ _ _).

    apply H.
    - solve_map_disjoint.
    - solve_map_disjoint.
    - assumption.
    - solve_map_disjoint.
    - solve_map_disjoint.
    - intros vₜ vₛ mt' ms' ? ? ?.
      subst. decompose_map_disjoint.

      rewrite (map_union_comm mtP mt3) by auto.
      rewrite (map_union_comm msP ms3) by auto.

      rewrite <- (map_union_assoc mt3 mtP mt').
      rewrite <- (map_union_assoc ms3 msP ms').

      apply Hpost.
      + solve_map_disjoint.
      + solve_map_disjoint.
      + do 4 eexists. repeat split.
        * solve_map_disjoint.
        * solve_map_disjoint.
        * assumption.
        * assumption.
  Qed.

  Lemma consequence C Γ Φ j fₜ pcₜ i fₛ pcₛ :
    ∀ P P' Φ',
    (⊨ P -* P') ->
    C | Γ ⊢ {{ P' }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ' }} ->
    (∀ vₜ vₛ, ⊨ Φ' vₜ vₛ -* Φ vₜ vₛ) ->
    C | Γ ⊢ {{ P }} fₜ @ pcₜ <{j, i}= fₛ @ pcₛ {{ Φ }}.
  Proof using Type.
    intros P P' Φ' HP H HΦ.
    intros Ψ mt2 ms2 ? ? Hpre mt3 ms3 ? ? Hpost.

    simp. apply H; auto.
    - rewrite <- (map_empty_union mt2).
      rewrite <- (map_empty_union ms2).
      apply HP; now auto.
    - intros vₜ vₛ mt ms ? ? HΦ'.
      apply Hpost; auto.
      rewrite <- (map_empty_union mt).
      rewrite <- (map_empty_union ms).
      apply HΦ.
      + solve_map_disjoint.
      + solve_map_disjoint.
      + assumption.
  Qed.
End Rules.
