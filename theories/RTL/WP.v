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

  Implicit Types Q : postcondition.

  Definition wp ρ f pc Q : logic :=
    fun n m => safe P (uncurry Q) ([], State f pc ρ, m) n.

  Lemma wp_ret ρ f pc Q :
    ∀ r v,
    f @ pc is <<{ ret r }>> ->
    ρ @ r ⇒ v ->
    ▷⌜Q v⌝ₘ ⊩ wp ρ f pc Q.
  Proof using Type.
    intros r v Hpc Hv.
    intros [] m Hwp; [apply safe_init | unfold_Prop].
    apply safe_to_step.
    - do 2 econstructor; eassumption || reflexivity.
    - intros t Hstep. inv Hstep. simregs.
      apply final_is_safe. econstructor.
      split.
      + reflexivity.
      + now unfold uncurry.
  Qed.

  Lemma wp_nop ρ f pc Q :
    ∀ pc',
    f @ pc is <<{ nop -> pc' }>> ->
    ▷wp ρ f pc' Q ⊩ wp ρ f pc Q.
  Proof using Type.
    intros v Hpc.
    intros [] m Hwp; [apply safe_init | unfold_Prop].
    apply safe_to_step.
    - do 2 econstructor; eassumption || reflexivity.
    - intros ? Hs.
      now inv Hs.
  Qed.

  Lemma wp_op ρ f pc Q :
    ∀ dst op args pc' vals v,
    f @ pc is <<{ dst := @op args -> pc' }>> ->
    ρ @ args ⇒ vals ->
    eval_op op vals = Some v ->
    ▷wp (⟦dst ⇐ v⟧ρ) f pc' Q ⊩ wp ρ f pc Q.
  Proof using Type.
    intros dst op args pc' vals v Hpc Hvals Hv.
    intros [] m Hwp; [apply safe_init | unfold_Prop].
    apply safe_to_step.
    - do 2 econstructor; eassumption || reflexivity.
    - intros ? Hs. inv Hs.
      now simregs.
  Qed.

  Lemma wp_load ρ f pc Q :
    ∀ dst src pc' addr v,
    f @ pc is <<{ dst := !src -> pc' }>> ->
    ρ @ src ⇒ addr ->
    (addr ↦ v ∧ ▷ wp (⟦dst ⇐ v⟧ρ) f pc' Q) ⊩ wp ρ f pc Q.
  Proof using Type.
    intros dst src pc' addr v Hpc Haddr.
    intros [] m (Hmem & Hwp); [apply safe_init | unfold_Prop].
    apply safe_to_step.
    - do 2 econstructor; eassumption || reflexivity.
    - intros ? Hs. inv Hs.
      now simregs.
  Qed.

  Lemma wp_store ρ f pc Q :
    ∀ dst src pc' addr v,
    f @ pc is <<{ !dst := src -> pc' }>> ->
    ρ @ dst ⇒ addr ->
    ρ @ src ⇒ v ->
    ▷⟦addr <- v⟧ wp ρ f pc' Q ⊩ wp ρ f pc Q.
  Proof using Type.
    intros dst src pc' addr v H Haddre Hmem.
    intros [] m Hwp; [apply safe_init | unfold_Prop].
    destruct Hwp as (m' & Hm' & Hwp). apply safe_to_step.
    - do 2 econstructor; eassumption || reflexivity.
    - intros ? Hs. inv Hs.
      now simregs.
  Qed.

  Lemma wp_cond ρ f pc Q :
    ∀ cond ifso ifnot v pc',
    f @ pc is <<{ if cond then goto ifso else goto ifnot }>> ->
    ρ @ cond ⇒ v ->
    (if (v =? 0)%Z then ifso else ifnot) = pc' ->
    ▷wp ρ f pc' Q ⊩ wp ρ f pc Q.
  Proof using Type.
    intros cond ifso ifnot v pc' H Hcond Hpc.
    intros [] m Hwp; [apply safe_init | unfold_Prop].
    apply safe_to_step.
    - do 2 econstructor; eassumption || reflexivity.
    - intros ? Hs. inv Hs.
      now simregs.
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

  Lemma wp_call ρ f pc Q :
    ∀ dst name args pc' vals fn Pre Post,
    f @ pc is <<{ dst := @call name args -> pc' }>> ->
    ρ @ args ⇒ vals ->
    find_fun P name = Some fn ->
    length (fn_regs fn) = length args ->
    hoare Pre fn Post ->
    (⌜Pre vals⌝ₘ ∧ ▷(∀ v, ⌜Post v⌝ₘ ⊩ₘ wp (⟦dst ⇐ v⟧ρ) f pc' Q)) ⊩
    wp ρ f pc Q.
  Proof using Type.
    intros dst sig args pc' vals fn Pre Post H Hargs Hfun Hlen Hspec.
    intros [|n] m (Hpre & Hwp); [apply safe_init | unfold_Prop ].
    apply safe_to_step.
    - do 2 econstructor; eassumption || reflexivity.
    - intros t Hs. inv Hs. simregs.
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
          rewrite Hlen.
          eapply regbank_list_length.
          eassumption.
        * lia.
      + eapply safe_implies_progress in Hrest.
        * eassumption.
        * apply Hwp.
          apply (hoare_post_from_steps _ _ _ Hspec) in Hrtc; auto.
        * lia.
  Qed.

  Local Lemma initial_context_exists : ∀ args regs,
    length args = length regs ->
    NoDup regs ->
    ∃ ρ, ρ @ regs ⇒ args.
  Proof using Type.
    intros args.
    induction args as [| v args IH]; intros regs Hlen Hdup.
    - exists ∅. symmetry in Hlen. rewrite (nil_length_inv _ Hlen).
      simregs.
    - simpl in Hlen. destruct regs as [| r regs]; inv Hlen as [ H ].
      apply NoDup_cons in Hdup.
      destruct Hdup as [Hr Hdup].
      destruct (IH _ H Hdup) as [ρ Hmap].
      exists (⟦r ⇐ v⟧ρ).
      apply regbank_assert_unfold.
      + simregs.
      + now apply regbank_set_discard_list.
  Qed.

  Lemma hoare_from_wp (Pre: precondition) f (Post: postcondition):
    (∀ ρ args,
       ρ @ (fn_regs f) ⇒ args ->
       ⌜Pre args⌝ₘ ⊩ wp ρ f (fn_entrypoint f) Post)
    -> hoare Pre f Post.
  Proof using Type.
    intros H args m [ ] Hlen Hpre; [apply safe_init | unfold_Prop ].
    apply safe_to_step.
    - destruct (initial_context_exists _ _ Hlen) as [ρ Hρ].
      + apply is_no_dup_sound. now apply fn_regs_no_dup.
      + do 2 econstructor; eassumption.
    - intros ? Hs. inv Hs.
      eapply H; eassumption || reflexivity.
  Qed.
End RTLWP.
