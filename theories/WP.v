From Stdlib Require Import Utf8.

From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.

From stdpp Require Import relations.
From stdpp Require Import tactics.

From RSL Require Import RTL.
From RSL Require Import Notations.
From RSL Require Import Semantics.
From RSL Require Import Logic.

Import RTLNotations.
Import ListNotations.

(* Set Mangle Names. *)

Section WP.
  Variable P : program.
 
  Inductive final (Q: postcondition) : state -> Prop :=
  | Final : ∀ v m, Q v m -> final Q ([], ReturnState v, m).

  Definition not_stuck t := ∃ u, P |- t ->> u.

  Lemma ret_not_stuck : ∀ frame σ v m,
    not_stuck (frame :: σ, ReturnState v, m).
  Proof. intros []. repeat econstructor; now eauto. Qed.

  Lemma ret_stuck_in_empty : ∀ v m,
    ~ not_stuck ([], ReturnState v, m).
  Proof. intros v m [u H]. inv H. Qed.

  Lemma lift_not_stuck : ∀ σ Σ s m,
    not_stuck (σ, s, m) ->
    not_stuck (σ ++ Σ, s, m).
  Proof. intros σ Σ s m [[[] ?] Ht]. eexists. apply lift_step. eassumption. Qed.

  (** [safeₙ Q n s] : s is a state that is safe for at most n steps:
      - s is a final step or
      - s is not stuck and can do at most n steps. *)
  Inductive safeₙ Q : state -> nat -> Prop :=
  | safe_init : ∀ s, safeₙ Q s 0
  | final_is_safe : ∀ s n, final Q s -> safeₙ Q s n
  | safe_to_step : ∀ s n,
    (* I am not stuck *)
    not_stuck s ->
    (* All possible next states are safe for at most n least *)
    (∀ t, P |- s ->> t -> safeₙ Q t n) ->
    (* I am safe for at most n+1 least *)
    safeₙ Q s (S n).

  Lemma safe_from_progress Q s n :
    (∀ t m,
       m <= n ->
       P |- s -{m}> t ->
       final Q t ∨ not_stuck t)
    -> safeₙ Q s n.
  Proof.
    induction n as [ | n IH] in s |- *; intros H.
    - constructor.
    - assert (Hstep: P |- s -{0}> s) by constructor.
      assert (Hle: 0 <= S n) by lia.
      destruct (H _ _ Hle Hstep) as [Hfin | Hns]; clear Hstep Hle.
      + now constructor.
      + apply safe_to_step; auto. intros t Hstep.
        apply IH. intros u m Heq Hsteps. subst.
        apply H with (S m).
        * lia.
        * econstructor; now eauto.
  Qed.

  Lemma safe_implies_progress Q s n :
    safeₙ Q s n ->
    ∀ t m, m < n -> P |- s -{m}> t -> final Q t ∨ not_stuck t.
  Proof.
    intros Hsafe.
    induction Hsafe as [s' | s' n' Hfin | s' n' Hns Hsafe IH]
      in n, Hsafe |- *; intros t m Hlt Hrtc.
    - inv Hlt.
    - destruct m as [ | m].
      + inv Hrtc. now left.
      + inv Hfin. apply nsteps_inv_l in Hrtc.
        destruct Hrtc as (? & Hstep & ?).
        inv Hstep.
    - destruct m as [ | m ].
      + inv Hrtc; now auto.
      + apply nsteps_inv_l in Hrtc.
        destruct Hrtc as (u & Hstep & Hrtc).
        eapply IH; try eassumption; lia.
  Qed.

  Definition safe_mono Q s :
    ∀ n m,
    m <= n ->
    safeₙ Q s n -> safeₙ Q s m.
  Proof.
    intros n m Hle Hsafe.
    induction Hsafe as [ | | ? ? Hns Hsafe IH ] in m, Hle |- *.
    - inv Hle. constructor.
    - now apply final_is_safe.
    - destruct m as [ | m ].
      + constructor.
      + apply safe_to_step.
        * assumption.
        * intros ? Ht. apply IH; auto. lia.
  Qed.

  Definition safe Q s := ∀ n, safeₙ Q s n.

  Definition wpₙ Q f pc : sProp :=
    fun ρ m n => safeₙ Q ([], State f pc ρ, m) n.

  Lemma wp_ret (Q: postcondition) f pc : ∀ r v,
    f@pc is <{ ret r }> ->
    ⊢ ▷ (r ↦ᵣ v ∧ ⌜Q v⌝ₘ) -> wpₙ Q f pc.
  Proof.
    intros r v Hpc ρ m [] H; [apply safe_init | ].
    unfold_Prop. destruct H as [Hv HQ]. subst.
    apply safe_to_step.
    - eexists; econstructor; now eauto.
    - intros t Hstep. inv Hstep. apply final_is_safe. now constructor.
  Qed.

  Lemma wp_nop Q f pc : ∀ pc',
    f@pc is <{ nop -> pc' }> ->
    ⊢ (▷ wpₙ Q f pc') -> wpₙ Q f pc.
  Proof.
    intros v Hpc ρ m [] Hwp; [apply safe_init | ].
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_op Q f pc : ∀ dst op args pc',
    f@pc is <{ dst := @op args -> pc' }> ->
    ⊢ ▷ (∀ vals,
           args ↦ᵣ vals ->
           ∃ v,
             ⌜eval_op op vals = Some v⌝ ∧ ⟦dst <-ᵣ v⟧wpₙ Q f pc'
        ) -> wpₙ Q f pc.
  Proof.
    intros dst op args pc' Hpc ρ m [] Hwp; [apply safe_init | ].
    destruct (Hwp _ eq_refl) as (v & Hv & Hwp'). unfold_Prop.
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_load Q f pc : ∀ dst src pc',
    f@pc is <{ dst := !src -> pc' }> ->
    ⊢ ▷ (∀ addr,
           src ↦ᵣ addr ->
           ∃ v, ⟦dst <-ᵣ v⟧ wpₙ Q f pc' ∧ addr ↦ v
        ) -> wpₙ Q f pc.
  Proof.
    intros dst src pc' Hpc ρ m [] Hwp; [apply safe_init | ].
    destruct (Hwp _ eq_refl) as (v & Hv & Hwp'). unfold_Prop.
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_store Q f pc : ∀ dst src pc',
    f@pc is <{ !dst := src -> pc' }> ->
    ⊢ ▷ (∀ addr v,
         dst ↦ᵣ addr ->
         src ↦ᵣ v ->
         ⟦addr <- v⟧ wpₙ Q f pc'
        ) -> wpₙ Q f pc.
  Proof.
    intros dst src pc' H ρ m [] Hwp; [apply safe_init | ].
    destruct (Hwp _ _ eq_refl eq_refl) as (v & Hv & Hwp'). unfold_Prop.
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_cond Q f pc : ∀ cond ifso ifnot,
    f@pc is <{ if cond then goto ifso else goto ifnot }> ->
    ⊢ ▷ (∀ v,
           cond ↦ᵣ v ->
           if (v =? 0)%Z
           then wpₙ Q f ifso
           else wpₙ Q f ifnot
        ) -> wpₙ Q f pc.
  Proof.
    intros cond ifso ifnot H ρ m [] Hwp; [apply safe_init | ].
    specialize (Hwp _ eq_refl). unfold_Prop. apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. inv Hs. now destruct (get_reg cond ρ =? 0)%Z.
  Qed.

  Definition hoare (Pre: precondition) f Post : Prop :=
    ∀ n args m, length args = length (fn_regs f) ->
                Pre args m ->
                safeₙ Post ([], CallState f args, m) n.

  Lemma hoare_post_from_steps (Pre: precondition) f (Post: postcondition) :
    hoare Pre f Post ->
    ∀ n args m v m',
    Pre args m ->
    P |- ([], CallState f args, m) -{ n }> ([], ReturnState v, m') ->
    Post v m'.
  Proof.
    intros Hspec n args m v m' Hpre Hsteps.
    eapply (safe_implies_progress Post) in Hsteps.
    - destruct Hsteps as [Hfin | Hstuck].
      + now inv Hfin.
      + apply ret_stuck_in_empty in Hstuck. tauto.
    - apply (Hspec (n + 1)); eauto. destruct n as [ | n].
      + inv Hsteps.
      + apply nsteps_inv_l in Hsteps. destruct Hsteps as (u & Hstep & Hsteps).
        now inv Hstep.
    - lia.
  Qed.

  Lemma wp_call f pc Q : ∀ dst name args pc',
    f@pc is <{ dst := @call name args -> pc' }> ->
    ⊢ ▷ (∀ vals,
           args ↦ᵣ vals ->
           ∃ fn Pre Post,
             ⌜find_fun P name = Some fn⌝ ∧
             ⌜length args = length (fn_regs fn)⌝ ∧
             ⌜hoare Pre fn Post⌝ ∧
             ⌜Pre vals⌝ₘ ∧
             (∀ v, ⊢ₘ ⌜Post v⌝ₘ -> ⟦dst <-ᵣ v⟧ wpₙ Q f pc')
        ) -> wpₙ Q f pc.
  Proof.
    intros dst sig args pc' H ρ m [ | n] Hwp; [apply safe_init | ].
    destruct (Hwp _ eq_refl)
      as (fn & Pre & Post & Hfun & Hlen & Hspec & Hpre & Hwp').
    clear Hwp. unfold_Prop. apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros t Hs. inv Hs.
      apply safe_from_progress.
      intros [[σ' s] m''] n' Hn Hsteps.
      apply unfold_call in Hsteps.
      destruct Hsteps as [(? & ? & Hrtc) | (? & ? & ? & ? & ? & Hrtc & Hrest)].
      + right. eapply safe_implies_progress in Hrtc;
          [destruct Hrtc as [Hfin | Hprogress] | | ].
        * inv Hfin. apply ret_not_stuck.
        * subst. now apply lift_not_stuck.
        * apply Hspec with (n := n+1); auto.
          unfold get_regs. now rewrite length_map.
        * lia.
      + eapply safe_implies_progress in Hrest.
        * eassumption.
        * apply Hwp'.
          apply (hoare_post_from_steps _ _ _ Hspec) in Hrtc; auto.
        * lia.
  Qed.

  Lemma hoare_from_wp Pre f Post:
    (
      (∃ args, ⌜Pre args⌝ₘ ∧ fn_regs f ↦ᵣ args) ⊢ wpₙ Post f (fn_entrypoint f)
    ) -> hoare Pre f Post.
  Proof.
    intros H [ |n ] args m Hlen Hpre; [apply safe_init | ].
    unfold_Prop.
    apply safe_to_step.
    - repeat econstructor; eauto.
    - intros ? Hs. inv Hs. apply H. eexists. split.
      + eassumption.
      + apply get_regs_init_regs.
        * apply fn_regs_no_dup.
        * assumption.
  Qed.

  Definition NodeInv Q f pc (NI : sProp) : Prop := ⊢ NI -> wpₙ Q f pc.

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

  Lemma test_inv :
    NodeInv (fun v m => (v = 10)%Z) test 3
      ⟨1 ↦ᵣ 1%Z ∧ 2 ↦ᵣ 10%Z ∧ ∃ v, 0 ↦ᵣ v ∧ ⌜(v <= 10)%Z⌝⟩.
  Proof.
    unfold NodeInv.
    intros ρ m n.
    revert ρ m.
    induction n as [ n IH ] using lt_wf_ind.
    (* apply löb. *)
    intros ρ m (Hone & Hten & v & Hres & Hv). unfold_Prop.
    eapply wp_op; auto. destruct n as [ | n]; try easy; unfold_Prop.
    intros ? <-. exists (10 - v)%Z; split; [now simpl_reg | ].
    eapply wp_cond; auto; destruct n as [ | n]; try easy; unfold_Prop.
    intros ? <-. simpl_reg.
    destruct (10 - v =? 0)%Z eqn:He.
    - apply Z.eqb_eq in He. assert (v = 10%Z) by lia. subst.
      eapply wp_ret with (v := 10%Z);
        auto; destruct n as [ | n]; try easy; unfold_Prop.
      split; simpl_reg.
    - apply Z.eqb_neq in He. assert ((v < 10)%Z) by lia.
      eapply wp_op; auto; destruct n as [ | n]; try easy; unfold_Prop.
      intros ? <-. exists (v + 1)%Z; split; [now simpl_reg | ].
      apply IH; repeat split; simpl_reg.
      eexists. split.
      + reflexivity.
      + lia.
  Qed.

  Lemma test_correct :
    hoare (fun args m => True) test (fun v m => (v = 10)%Z).
  Proof.
    apply hoare_from_wp.
    intros ρ m n _. unfold_Prop.
    eapply wp_op; auto; destruct n as [ | n]; try easy; unfold_Prop.
    intros ? <-. exists 0%Z; split; [now simpl_reg |].
    eapply wp_op; auto; destruct n as [ | n]; try easy; unfold_Prop.
    intros ? <-. exists 1%Z; split; [now simpl_reg |].
    eapply wp_op; auto; destruct n as [ | n]; try easy; unfold_Prop.
    intros ? <-. exists 10%Z; split; [now simpl_reg |].
    apply test_inv; unfold_Prop. repeat split; simpl_reg.
    eexists. split.
    - reflexivity.
    - lia.
  Qed.
End WP.
