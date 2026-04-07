From Stdlib Require Import Utf8.

From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.

From stdpp Require Import relations.

From RSL Require Import RTL.
From RSL Require Import Notations.
From RSL Require Import Semantics.
From RSL Require Import Logic.
From RSL Require Import Tactics.

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
  Inductive safeₙ (Q : postcondition) : state -> nat -> Prop :=
  | safe_init : ∀ s, safeₙ Q s 0
  | final_is_safe : ∀ s, final Q s -> ∀ n, safeₙ Q s n
  | safe_to_step : ∀ s n,
    (* I am not stuck *)
    not_stuck s ->
    (* All possible next states are safe for at most n least *)
    (∀ t, P |- s ->> t -> safeₙ Q t n) ->
    (* I am safe for at most n+1 least *)
    safeₙ Q s (S n).

  Lemma safe_weakening Q s n :
    ∀ m,
    m <= n ->
    safeₙ Q s n ->
    safeₙ Q s m.
  Proof.
    intros m Hle Hsafe.
    induction Hsafe as [s' | s' Hfin n' | s' n' Hns Hstep IH] in m, Hle |- *.
    - inv Hle. constructor.
    - now constructor.
    - destruct m as [ |m].
      + constructor.
      + apply safe_to_step; auto.
        intros t Ht.
        apply IH; auto.
        lia.
  Qed.

  Lemma safe_from_progress Q s n :
    (∀ t m,
       m <= n ->
       P |- s -{m}> t ->
       final Q t ∨ not_stuck t)
    -> safeₙ Q s n.
  Proof.
    intros H.
    induction n as [ |n IH] in s, H |- *.
    - apply safe_init.
    - assert (Hstep: P |- s -{0}> s) by constructor.
      assert (Hle: 0 <= S n) by lia.
      destruct (H s 0 Hle Hstep) as [Hfin | Hns];
        clear Hstep Hle.
      + now constructor.
      + apply safe_to_step; auto. intros t Hstep.
        apply IH. intros u m Hle Hsteps.
        apply (H u (S m)).
        -- lia.
        -- econstructor; now eauto.
  Qed.

  Lemma safe_implies_progress Q s n :
    safeₙ Q s n ->
    ∀ m t, m < n ->
           P |- s -{m}> t ->
           final Q t ∨ not_stuck t.
  Proof.
    intros Hsafe.
    induction Hsafe as [s' | s' Hfin n' | s' n' Hns Hsafe IH];
      intros m t Hlt Hrtc.
    - inv Hlt.
    - destruct m.
      + inv Hrtc. auto.
      + apply nsteps_inv_l in Hrtc. destruct Hrtc as (? & H & ?).
        inv Hfin. inv H.
    - destruct m.
      + inv Hrtc. auto.
      + apply nsteps_inv_l in Hrtc.
        destruct Hrtc as (u & Hstep & Hrtc).
        eapply IH; eauto. lia.
  Qed.

  Definition safe Q s := ∀ n, safeₙ Q s n.

  Definition wp__n Q f pc : sProp :=
    fun n '(ρ, m) => safeₙ Q ([], State f pc ρ, m) n.

  Lemma wp_ret f pc Q : ∀ v,
    f@pc is <{ ret v }> ->
    (λₛ ρ m, ⌜Q (get_reg ρ v) m⌝) ⊢ wp__n Q f pc.
  Proof.
    intros v H [] [ρ m] HQ; [apply safe_init | ].
    apply safe_to_step.
    - eexists; econstructor; now eauto.
    - intros t Hstep. inv Hstep. apply final_is_safe. now constructor.
  Qed.

  Lemma wp_nop f pc Q : forall pc',
    f@pc is <{ nop -> pc' }> ->
    ▷ wp__n Q f pc' ⊢ wp__n Q f pc.
  Proof.
    intros v H [] [ρ m] Hwp; [apply safe_init | ].
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_op f pc Q : forall dst op args pc',
    f@pc is <{ dst := @op args -> pc' }> ->
    ▷ (λₛ ρ m,
         ∃ v,
           ⌜eval_op op (get_regs ρ args) = Some v⌝
           ∧ wp__n Q f pc' ⟨ set_reg ρ dst v, m ⟩
    ) ⊢ wp__n Q f pc.
  Proof.
    intros dst op args pc' H [] [ρ m] Hwp; [apply safe_init | ].
    destruct Hwp as (v & Hv & Hwp). unfold_sProp.
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_load f pc Q : forall dst src pc',
    f@pc is <{ dst := !src -> pc' }> ->
    ▷ (λₛ ρ m,
         let addr := get_reg ρ src in
         ∃ v, ⌜get_at m addr = Some v⌝
              ∧ wp__n Q f pc' ⟨ set_reg ρ dst v, m ⟩
    ) ⊢ wp__n Q f pc.
  Proof.
    intros dst src pc' H [] [ρ m] Hwp; [apply safe_init | ].
    destruct Hwp as (v & Hv & Hwp). unfold_sProp.
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_store f pc Q : forall dst src pc',
    f@pc is <{ !dst := src -> pc' }> ->
    ▷ (λₛ ρ m,
         let addr := get_reg ρ dst in
         let v := get_reg ρ src in
         ∃ m', ⌜set_at m addr v = Some m'⌝
               ∧ wp__n Q f pc' ⟨ ρ, m' ⟩
    ) ⊢ wp__n Q f pc.
  Proof.
    intros dst src pc' H [] [ρ m] Hwp; [apply safe_init | ].
    destruct Hwp as (v & Hv & Hwp). unfold_sProp.
    apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Lemma wp_cond f pc Q : forall cond ifso ifnot,
    f@pc is <{ if cond then goto ifso else goto ifnot }> ->
    ▷ (λₛ ρ m,
         wp__n Q f (if (get_reg ρ cond =? 0)%Z then ifso else ifnot)
      ) ⊢ wp__n Q f pc.
  Proof.
    intros cond ifso ifnot H [] [ρ m] Hwp; [apply safe_init | ].
    unfold_sProp. apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros ? Hs. now inv Hs.
  Qed.

  Definition precondition : Type := list val -> memory -> Prop.

  Definition hoare (P: precondition) (f: function) (Q: postcondition) : Prop
    := ∀ args m, P args m -> safe Q ([], CallState f args, m).

  Notation "'{{' P '}}' f '{{' Q '}}'" :=
    (hoare P f Q) (at level 90, f at next level).

  Lemma hoare_post_from_steps Pre f Post :
    {{ Pre }} f {{ Post }} ->
    ∀ n args m v m',
    P |- ([], CallState f args, m) -{n}> ([], ReturnState v, m') ->
    Pre args m ->
    Post v m'.
  Proof.
    intros Hspec n args m v m' Hsteps Hpre.
    eapply safe_implies_progress with (n := S n) in Hsteps.
    - destruct Hsteps as [Hfin | Hstuck].
      + inv Hfin. eassumption.
      + apply ret_stuck_in_empty in Hstuck. tauto.
    - now apply Hspec.
    - lia.
  Qed.

  Lemma wp_call f pc Q : ∀ dst sig args pc',
    f@pc is <{ dst := @call sig args -> pc' }> ->
    ▷ (λₛ ρ m,
         ∃ fn Pre Post,
           let vals := get_regs ρ args in
           ⌜find_fun P sig = Some fn⌝ ∧
           ⌜{{ Pre }} fn {{ Post }}⌝ ∧
           ⌜Pre vals m⌝ ∧
           ∀ v m', ⌜Post v m'⌝ -> wp__n Q f pc' ⟨ set_reg ρ dst v, m' ⟩
      ) ⊢ wp__n Q f pc.
  Proof.
    intros dst sig args pc' H [ | n] [ρ m] Hwp; [apply safe_init | ].
    destruct Hwp as (fn & Pre & Post & Hfun & Hspec & Hpre & Hwp).
    unfold_sProp. apply safe_to_step.
    - repeat econstructor; now eauto.
    - intros t Hs. inv Hs.
      apply safe_from_progress.
      intros [[σ' s] m''] n' Hn Hsteps.
      apply unfold_call in Hsteps.
      destruct Hsteps as [(? & ? & Hrtc) | (? & ? & ? & ? & ? & Hrtc & Hrest)].
      + right. pose proof (Hspec _ _ Hpre (S n)) as Hfunsafe.
        edestruct (safe_implies_progress _ _ _ Hfunsafe n')
          as [Hfin | Hprogress]; eauto with lia.
        * inv Hfin. apply ret_not_stuck.
        * subst. now apply lift_not_stuck.
      + eapply safe_implies_progress in Hrest.
        * eassumption.
        * apply Hwp.
          apply (hoare_post_from_steps _ _ _ Hspec) in Hrtc; auto.
        * lia.
  Qed.
End WP.

(* Lemma wp_truc f pc Q : *)
(*   ▷ ((∀ l ∈ L, ∀ ρ m, wp f l Q (ρ, m)) -> ∀ l ∈ L, ∀ ρ m, wp f l Q (ρ, m)) *)
(*   ->∀ pc ∈ L,∀ ρ m, -> wp f pc Q (ρ, m). *)
(* Proof. *)
