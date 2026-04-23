From stdpp Require Import prelude.
From stdpp Require Import strings.

From RSL Require Import Commons.Utils.
From RSL Require Import Commons.Language.
From RSL Require Import Commons.WP.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Logic.

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
        * apply fn_regs_no_dup.
        * assumption.
  Qed.

  Definition NodeInv Q f pc (NI : logic) : Prop := ⊢ NI -> wp Q f pc.

  Definition body : code :=
    let x := 0 in
    let one := 1 in
    let ten := 2 in
    let diff := 3 in
    <{{
          0: x := #0 -> 1;
          1: one := #1 -> 2;
          2: ten := #10 -> 3;
          3: diff := ten - x -> 4;
          4: if diff then goto 6 else goto 5;
          5: x := x + one -> 3;
          6: ret x;
      }}>.

  Definition test : function :=
    {|
      fn_name := "test"%string;
      fn_regs := [];
      fn_entrypoint := 0;
      fn_code := body;
      fn_regs_no_dup := NoDup_nil_2;
    |}.

  Ltac step lemma :=
    match goal with
    | |- wp _ ?f ?pc _ _ ?n =>
        let H := fresh "Hpc" in
        eassert (H: f@pc is _) by reflexivity;
        eapply lemma;
        [now apply H|];
        clear H; repeat split; simpl_reg; unfold_Prop; simpl;
        try (destruct n as [|n]; [easy|])
    | |- match ?n with
         | O => True
         | S n' => wp _ _ _ _ _ n'
         end => destruct n as [|n]; [easy|step lemma]
    end.

  Lemma test_inv :
    NodeInv (fun v m => v = 10%Z) test 3
      ⟨1 ↦ᵣ 1%Z ∧ 2 ↦ᵣ 10%Z ∧ ∃ v, 0 ↦ᵣ v ∧ ⌜(v <= 10)%Z⌝⟩.
  Proof.
    apply löb.
    intros ρ m n IH (Hone & Hten & v & Hres & Hv).
    step wp_op.
    step wp_cond.
    destruct (10 - v =? 0)%Z eqn:He.
    - step wp_ret. repeat split. simpl_reg.
    - step wp_op. eapply safe_mono; [|apply IH].
      + lia.
      + simpl_reg. eexists. repeat split.
        lia.
  Qed.

  Lemma test_correct :
    hoare (fun args m => True) test (fun v m => v = 10%Z).
  Proof.
    apply hoare_from_wp.
    intros args ρ m n _.
    step wp_op.
    step wp_op.
    step wp_op.
    apply test_inv. repeat (simpl_reg; unfold_Prop).
    eexists. repeat split. lia.
  Qed.
End RTLWP.
