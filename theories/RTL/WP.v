From RSL Require Import Prelude.

From RSL Require Import Commons.WP.
From RSL Require Import Commons.Logic.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.Semantics.

Import RTLNotations.

(* Set Mangle Names. *)

Section RTLWP.
  Let Λ : lang := rtl_lang.
  Context (P: prog Λ).

  Definition wp (Q: postcondition) f pc : logic :=
    fun ρ m n => safe P (uncurry Q) ([], State f pc ρ, m) n.

  Lemma wp_ret (Q: postcondition) f pc : ∀ r v,
    f@pc is <{ ret r }> ->
    ⊢ ▷ (r ↦ᵣ v ∧ ⌜Q v⌝ₘ) -> wp Q f pc.
  Proof.
    intros r v Hpc ρ m [] H; [apply safe_init | ].
    unfold_Prop. destruct H as [Hv HQ]. subst.
    apply safe_to_step.
    - eexists; econstructor; now eauto.
    - intros t Hstep. inv Hstep. apply final_is_safe. econstructor.
      split.
      + reflexivity.
      + now unfold uncurry.
  Qed.

  Lemma wp_nop Q f pc : ∀ pc',
    f@pc is <{ nop -> pc' }> ->
    ⊢ (▷ wp Q f pc') -> wp Q f pc.
  Proof.
    intros v Hpc ρ m [] Hwp; [apply safe_init | ].
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_op Q f pc : ∀ dst op args pc' vals v,
    f@pc is <{ dst := @op args -> pc' }> ->
    ⊢ (args ↦ᵣ vals ∧
       ⌜eval_op op vals = Some v⌝ ∧
       ▷ ⟦dst <-ᵣ v⟧wp Q f pc') ->
    wp Q f pc.
  Proof.
    intros dst op args pc' vals v Hpc ρ m [] (Hargs & Hv & Hwp);
      [apply safe_init | ]. unfold_Prop. subst.
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_load Q f pc : ∀ dst src pc' addr v,
    f@pc is <{ dst := !src -> pc' }> ->
    ⊢ (src ↦ᵣ addr ∧ addr ↦ v ∧ ▷ ⟦dst <-ᵣ v⟧ wp Q f pc') ->
    wp Q f pc.
  Proof.
    intros dst src pc' addr v Hpc ρ m [] (Haddr & Hmem & Hwp)
    ; [apply safe_init | ]. unfold_Prop. subst.
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_store Q f pc : ∀ dst src pc' addr v,
    f@pc is <{ !dst := src -> pc' }> ->
    ⊢ (dst ↦ᵣ addr ∧
       src ↦ᵣ v ∧
       ▷ ⟦addr <- v⟧ wp Q f pc') ->
    wp Q f pc.
  Proof.
    intros dst src pc' addr v H ρ m [] (Haddr & Hmem & Hwp);
      [apply safe_init | ]. unfold_Prop. subst.
    destruct Hwp as (m' & Hm' & Hwp). apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_cond Q f pc : ∀ cond ifso ifnot v,
    f@pc is <{ if cond then goto ifso else goto ifnot }> ->
    ⊢ (cond ↦ᵣ v ∧
       if (v =? 0)%Z
       then ▷ wp Q f ifso
       else ▷ wp Q f ifnot) ->
    wp Q f pc.
  Proof.
    intros cond ifso ifnot v H ρ m [] (Hv & Hwp); [apply safe_init | ].
    unfold_Prop. apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. inv Hs. now destruct (get_reg cond ρ =? 0)%Z.
  Qed.

  Definition hoare (Pre: precondition) f (Post: postcondition) : Prop :=
    ∀ args m n, length args = length (fn_regs f) ->
                Pre args m ->
                safe P (uncurry Post) ([], CallState f args, m) n.

  Lemma hoare_post_from_steps (Pre: precondition) f (Post: postcondition) :
    hoare Pre f Post ->
    ∀ n args m v m',
    Pre args m ->
    P ⊨ ([], CallState f args, m) -{ n }> ([], ReturnState v, m') ->
    Post v m'.
  Proof.
    intros Hspec n args m v m' Hpre Hsteps.
    eapply safe_implies_progress with (Q := uncurry Post) in Hsteps.
    - destruct Hsteps as [Hfin | Hstuck].
      + destruct Hfin as (x & Hfin & HQ). inv Hfin. apply HQ.
      + now apply ret_stuck_in_empty in Hstuck.
    - apply (Hspec _ _ (n + 1)); eauto. destruct n as [ | n].
      + inv Hsteps.
      + apply nsteps_inv_l in Hsteps. destruct Hsteps as (u & Hstep & Hsteps).
        now inv Hstep.
    - lia.
  Qed.

  Lemma wp_call f pc Q : ∀ dst name args pc' vals fn Pre Post,
    f@pc is <{ dst := @call name args -> pc' }> ->
    ⊢ (args ↦ᵣ vals ∧
       ⌜find_fun P name = Some fn⌝ ∧
       ⌜length args = length (fn_regs fn)⌝ ∧
       ⌜hoare Pre fn Post⌝ ∧
       ⌜Pre vals⌝ₘ ∧
       ▷ (∀ v, ⊢ₘ ⌜Post v⌝ₘ -> ⟦dst <-ᵣ v⟧ wp Q f pc')) ->
    wp Q f pc.
  Proof.
    intros dst sig args pc' vals fn Pre Post H ρ m [ | n]
      (Hargs & Hfun & Hlen & Hspec & Hpre & Hwp); [apply safe_init | ].
    unfold_Prop. subst.
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros t Hs. inv Hs.
      apply safe_from_progress.
      intros [[σ' s] m''] n' Hn Hsteps.
      apply unfold_call in Hsteps.
      destruct Hsteps as [(? & ? & Hrtc) | (? & ? & ? & ? & ? & Hrtc & Hrest)].
      + right. eapply safe_implies_progress with (Q := uncurry Post) in Hrtc;
          [destruct Hrtc as [Hfin | Hprogress] | | ].
        * destruct Hfin as ([] & Hfin & ?).
          apply is_final_struct in Hfin. inv Hfin.
          apply ret_not_stuck.
        * subst. now apply lift_not_stuck.
        * apply Hspec with (n := n+1); auto.
          unfold get_regs. now rewrite length_map.
        * lia.
      + eapply safe_implies_progress in Hrest.
        * eassumption.
        * apply Hwp.
          apply (hoare_post_from_steps _ _ _ Hspec) in Hrtc; auto.
        * lia.
  Qed.

  Lemma hoare_from_wp (Pre: precondition) f (Post: postcondition):
    (∀ args,
       ⊢ (⌜Pre args⌝ₘ ∧ fn_regs f ↦ᵣ args) -> wp Post f (fn_entrypoint f))
    -> hoare Pre f Post.
  Proof.
    intros H args m [ ] Hlen Hpre; [apply safe_init | ].
    unfold_Prop.
    apply safe_to_step.
    - repeat econstructor; eauto.
    - intros ? Hs. inv Hs. apply H with args. split.
      + eassumption.
      + apply get_regs_init_regs.
        * apply is_no_dup_sound. apply fn_regs_no_dup.
        * assumption.
  Qed.
End RTLWP.
