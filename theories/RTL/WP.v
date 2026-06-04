From RSL Require Import Prelude.

From RSL Require Import Commons.WP.
From RSL Require Import Commons.Logic.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.Semantics.

Import RTLNotations.

Section RTLWP.
  Let Λ : lang := rtl_lang.
  Context (P: prog Λ).

  Definition wp (Q: postcondition) f pc : logic :=
    fun ρ m n => safe P (uncurry Q) ([], State f pc ρ, m) n.

  Lemma wp_ret (Q: postcondition) f pc : ∀ r v,
    f@pc is <{ ret r }> ->
    ⊢ ▷ (r ⇒ v ∧ ⌜Q v⌝ₘ) -> wp Q f pc.
  Proof using Type.
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
  Proof using Type.
    intros v Hpc ρ m [] Hwp; [apply safe_init | ].
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_op Q f pc : ∀ dst op args pc' vals v,
    f@pc is <{ dst := @op args -> pc' }> ->
    ⊢ (args ⇒ vals ∧
       ⌜eval_op op vals = Some v⌝ ∧
       ▷ ⟦dst ⇐ v⟧wp Q f pc') ->
    wp Q f pc.
  Proof using Type.
    intros dst op args pc' vals v Hpc ρ m [] (Hargs & Hv & Hwp);
      [apply safe_init | ]. unfold_Prop. subst.
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_load Q f pc : ∀ dst src pc' addr v,
    f@pc is <{ dst := !src -> pc' }> ->
    ⊢ (src ⇒ addr ∧ addr ↦ v ∧ ▷ ⟦dst ⇐ v⟧ wp Q f pc') ->
    wp Q f pc.
  Proof using Type.
    intros dst src pc' addr v Hpc ρ m [] (Haddr & Hmem & Hwp)
    ; [apply safe_init | ]. unfold_Prop. subst.
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_store Q f pc : ∀ dst src pc' addr v,
    f@pc is <{ !dst := src -> pc' }> ->
    ⊢ (dst ⇒ addr ∧
       src ⇒ v ∧
       ▷ ⟦addr <- v⟧ wp Q f pc') ->
    wp Q f pc.
  Proof using Type.
    intros dst src pc' addr v H ρ m [] (Haddr & Hmem & Hwp);
      [apply safe_init | ]. unfold_Prop. subst.
    destruct Hwp as (m' & Hm' & Hwp). apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_cond Q f pc : ∀ cond ifso ifnot v,
    f@pc is <{ if cond then goto ifso else goto ifnot }> ->
    ⊢ (cond ⇒ v ∧
       if (v =? 0)%Z
       then ▷ wp Q f ifso
       else ▷ wp Q f ifnot) ->
    wp Q f pc.
  Proof using Type.
    intros cond ifso ifnot v H ρ m [] (Hv & Hwp); [apply safe_init | ].
    unfold_Prop. apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. inv Hs. now destruct (get_reg ρ cond =? 0)%Z.
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
  Proof using Type.
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
    ⊢ (args ⇒ vals ∧
       ⌜find_fun P name = Some fn⌝ ∧
       ⌜length (fn_regs fn) = length args⌝ ∧
       ⌜hoare Pre fn Post⌝ ∧
       ⌜Pre vals⌝ₘ ∧
       ▷ (∀ v, ⊢ₘ ⌜Post v⌝ₘ -> ⟦dst ⇐ v⟧ wp Q f pc')) ->
    wp Q f pc.
  Proof using Type.
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
          now rewrite length_map.
        * lia.
      + eapply safe_implies_progress in Hrest.
        * eassumption.
        * apply Hwp.
          apply (hoare_post_from_steps _ _ _ Hspec) in Hrtc; auto.
        * lia.
  Qed.

  Local Lemma get_regs_not_in : ∀ regs args r ρ v,
    r ∉ regs ->
    map (get_reg ρ) regs = args ->
    map (get_reg (<[r:=v]> ρ)) regs = args.
  Proof using Type.
    intros regs args r ρ v Hr Hmap.
    induction args as [| a args IH ] in regs, Hmap, Hr |- *.
    - apply map_eq_nil in Hmap. now subst regs.
    - apply map_eq_cons in Hmap.
      destruct Hmap as (reg & tl & -> & Hreg & Hmap).
      apply not_elem_of_cons in Hr.
      destruct Hr as [Hr Htl].
      simpl. f_equal.
      + unfold get_reg. now rewrite (fin_maps.lookup_insert_ne ρ).
      + now apply IH.
  Qed.

  Local Lemma initial_context_exists : ∀ args regs,
    length args = length regs ->
    NoDup regs ->
    ∃ ρ, map (get_reg ρ) regs = args.
  Proof using Type.
    intros args.
    induction args as [| v args IH]; intros regs Hlen Hdup.
    - exists ∅. symmetry in Hlen. now rewrite (nil_length_inv _ Hlen).
    - simpl in Hlen. destruct regs as [| r regs]; inv Hlen as [ H ].
      apply NoDup_cons in Hdup.
      destruct Hdup as [Hr Hdup].
      destruct (IH _ H Hdup) as [ρ Hmap].
      exists (<[r := v]>ρ).
      simpl. f_equal.
      + unfold get_reg. now rewrite (fin_maps.lookup_insert_eq ρ).
      + now apply get_regs_not_in.
  Qed.

  Lemma hoare_from_wp (Pre: precondition) f (Post: postcondition):
    (∀ args,
       ⊢ (⌜Pre args⌝ₘ ∧ fn_regs f ⇒ args) -> wp Post f (fn_entrypoint f))
    -> hoare Pre f Post.
  Proof using Type.
    intros H args m [ ] Hlen Hpre; [apply safe_init | ].
    unfold_Prop.
    apply safe_to_step.
    - destruct (initial_context_exists _ _ Hlen) as [ρ Hρ].
      + apply is_no_dup_sound. now apply fn_regs_no_dup.
      + do 2 econstructor; eassumption.
    - intros ? Hs. inv Hs. eapply H. split; eassumption || reflexivity.
  Qed.
End RTLWP.
