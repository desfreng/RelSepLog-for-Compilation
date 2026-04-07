From Stdlib Require Import Utf8.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.Relations.

From stdpp Require Import gmap.

From RSL Require Import RTL.
From RSL Require Import Notations.
From RSL Require Import Semantics.
From RSL Require Import Tactics.
From RSL Require Import WP.

Import RTLNotations.
Import ListNotations.

Section WPGenerator.
  Variable P : program.

  Definition node_inv : Type := node -> regmap * memory -> Prop.

  (* Record inv_sound (f : function) (I : node_inv) (Q : postcondition) : Prop := *)
  (* { *)
  (*   sound_ret : ∀ pc v, *)
  (*     f@pc is <{ ret v }> -> *)
  (*     ∀ ρ m, I pc (ρ, m) -> Q (get_reg ρ v) m *)

  (* ; sound_nop : ∀ pc pc', *)
  (*     f@pc is <{ nop -> pc' }> -> *)
  (*     ∀ ρ m, I pc (ρ, m) -> I pc' (ρ, m) *)

  (* ; sound_op : ∀ pc dst op args pc', *)
  (*     f@pc is <{ dst := @op args -> pc' }> -> *)
  (*     ∀ ρ m, I pc (ρ, m) -> *)
  (*            ∃ v, *)
  (*              eval_op op (get_regs ρ args) = Some v *)
  (*              ∧ I pc' (set_reg ρ dst v, m) *)

  (* ; sound_load : ∀ pc dst src pc', *)
  (*     f@pc is <{ dst := !src -> pc' }> -> *)
  (*     ∀ ρ m, I pc (ρ, m) -> *)
  (*            ∃ v, *)
  (*              get_at m (get_reg ρ src) = Some v *)
  (*              ∧ I pc' (set_reg ρ dst v, m) *)

  (* ; sound_store : ∀ pc dst src pc', *)
  (*     f@pc is <{ !dst := src -> pc' }> -> *)
  (*     ∀ ρ m, I pc (ρ, m) -> *)
  (*            ∃ m', *)
  (*              set_at m (get_reg ρ dst) (get_reg ρ src) = Some m' *)
  (*              ∧ I pc' (ρ, m') *)

  (* ; sound_cond : ∀ pc cond ifso ifnot, *)
  (*     f@pc is <{ if cond then goto ifso else goto ifnot }> -> *)
  (*     ∀ ρ m, I pc (ρ, m) -> *)
  (*            if (get_reg ρ cond =? 0)%Z *)
  (*            then I ifso (ρ, m) *)
  (*            else I ifnot (ρ, m) *)

  (* ; sound_call : ∀ pc dst sig args pc', *)
  (*     f@pc is <{ dst := @call sig args -> pc' }> -> *)
  (*     ∀ ρ m, I pc (ρ, m) -> *)
  (*            ∃ fn Pre Post, *)
  (*              find_fun P sig = Some fn *)
  (*              ∧ hoare P Pre fn Post *)
  (*              ∧ Pre (get_regs ρ args) m *)
  (*              ∧ ∀ v m', Post v m' -> I pc' (set_reg ρ dst v, m') *)

  (* ; inv_not_defined : ∀ pc, *)
  (*     (fn_code f) !! pc = None -> ∀ ρ m, I pc (ρ, m) = False *)
  (* }. *)

  (* Lemma inv_progress f I Q : *)
  (*   inv_sound f I Q -> *)
  (*   ∀ pc ρ m, I pc (ρ, m) -> ∃ u, P ⊢ ([], State f pc ρ, m) ->> u. *)
  (* Proof. *)
  (*   intros Hsound pc ρ m HI. *)
  (*   destruct ((fn_code f) !! pc) as [[] | ] eqn:Hinstr. *)
  (*   - eexists; econstructor; now eauto. *)
  (*   - edestruct sound_op as (v' & Hv' & _); eauto. *)
  (*     eexists. econstructor; now eauto. *)
  (*   - edestruct sound_load as (v' & Hv' & _); eauto. *)
  (*     eexists. econstructor; now eauto. *)
  (*   - edestruct sound_store as (v' & Hv' & _); eauto. *)
  (*     eexists. econstructor; now eauto. *)
  (*   - edestruct sound_call as (fn & _ & _ & Hfun & _); eauto. *)
  (*     eexists. econstructor; now eauto. *)
  (*   - eexists; econstructor; now eauto. *)
  (*   - eexists; econstructor; now eauto. *)
  (*   - rewrite (inv_not_defined _ _ _ Hsound _ Hinstr) in HI. *)
  (*     contradiction. *)
  (* Qed. *)

  (* Lemma inv_implies_wp f I Q : *)
  (*   inv_sound f I Q -> *)
  (*   ∀ pc ρ m, I pc (ρ, m) -> wp P f pc Q (ρ, m). *)
  (* Proof. *)
  (*   intros Hsound pc ρ m HI t Hrtc. *)
  (*   apply rtc_nsteps in Hrtc. destruct Hrtc as [n Hnsteps]. *)
  (*   revert pc ρ m t HI Hnsteps. *)
  (*   induction n as [ n IH] using lt_wf_ind. *)
  (*   intros pc ρ m t HI Hnsteps. destruct n as [ | n ]. *)
  (*   - inv Hnsteps. right. eapply inv_progress; eassumption. *)
  (*   - apply nsteps_inv_l in Hnsteps. *)
  (*     destruct Hnsteps as (y & Hstep & Hnsteps). *)
  (*     inv Hstep; try (apply (IH n) in Hnsteps; auto). *)
  (*     + eapply sound_nop; eauto. *)
  (*     + apply rtc_nsteps_2 in Hnsteps. *)
  (*       apply ret_no_step in Hnsteps. subst. *)
  (*       left. constructor. eapply sound_ret; eassumption. *)
  (*     + edestruct sound_op as (v' & Hv' & HI'); eauto; now some_inj. *)
  (*     + edestruct sound_load as (v' & Hv' & HI'); eauto; now some_inj. *)
  (*     + edestruct sound_store as (v' & Hv' & HI'); eauto; now some_inj. *)
  (*     + assert (Hif: _) by (eapply sound_cond; eauto; now some_inj). *)
  (*       now case_if Hif. *)
  (*     + edestruct sound_call *)
  (*         as (fn' & Pre & Post & Hfun & Hspec & HPre & Hwp); eauto; some_inj. *)
  (*       destruct t as [[] ?]; apply unfold_call in Hnsteps; *)
  (*         destruct Hnsteps as *)
  (*         [(σ' & Hσ & Hfun) | (m1 & m2 & v & m'' & -> & Hfun & Hrtc)]; *)
  (*         pose proof (rtc_nsteps_2 _ _ _ Hfun) as Hfun'; *)
  (*         edestruct (Hspec _ _ HPre _ Hfun') as [Hfin | (u & Hu)]. *)
  (*       * inv Hfin. right. eexists. econstructor; now eauto. *)
  (*       * right. destruct u as [[] ?]. subst. eexists. *)
  (*         apply lift_step. eassumption. *)
  (*       * inv Hfin. eapply (IH m2). 1: lia. 2: eassumption. *)
  (*         now apply Hwp. *)
  (*       * inv Hu. *)
  (* Qed. *)

  (* Lemma hoare_from_inv f I : ∀ Pre Post, *)
  (*   inv_sound f I Post -> *)
  (*   (∀ args m, *)
  (*      Pre args m -> *)
  (*      I (fn_entrypoint f) (init_regs args (in_regs (fn_sig f)), m)) -> *)
  (*   hoare P Pre f Post. *)
  (* Proof. *)
  (*   intros Pre Post Hsound Hpre args m Hpre_args t Hrtc. *)
  (*   apply rtc_inv in Hrtc. *)
  (*   destruct Hrtc as [ <- | (ss & Hstep & Hrtc )]. *)
  (*   - right. eexists. eapply exec_function. reflexivity. *)
  (*   - inv Hstep. eapply inv_implies_wp; eauto. *)
  (* Qed. *)


  (* Definition my_code : code := <{{ *)
  (*         1: nop -> 2; *)
  (*         2: $1 := #32 -> 3; *)
  (*         3: $1 := $2 -> 4; *)
  (*         4: $1 := $2 + $3 -> 5; *)
  (*         5: $1 := $2 * $3 -> 6; *)
  (*         6: $1 := !2 -> 7; *)
  (*         7: !1 := $2 -> 8; *)
  (*         8: if $1 then goto 9 else goto 9; *)
  (*         9: ret $1; *)
  (*     }}>. *)

  (* Definition check_pc_inv I Q '(pc, instr) : regmap -> memory -> Prop := *)
  (*   match instr with *)
  (*   | <{ ret v }> => *)
  (*       fun ρ m => I pc (ρ, m) -> Q (get_reg ρ v) m *)
  (*   | <{ nop -> pc' }> => *)
  (*       fun ρ m => I pc (ρ, m) -> I pc' (ρ, m) *)
  (*   | <{ dst := @op args -> pc' }> => *)
  (*       fun ρ m => *)
  (*         I pc (ρ, m) -> *)
  (*         ∃ v, *)
  (*           eval_op op (get_regs ρ args) = Some v *)
  (*           ∧ I pc' (set_reg ρ dst v, m) *)
  (*   | <{ dst := !src -> pc' }> => *)
  (*       fun ρ m => *)
  (*         I pc (ρ, m) -> *)
  (*         ∃ v, *)
  (*           get_at m (get_reg ρ src) = Some v *)
  (*           ∧ I pc' (set_reg ρ dst v, m) *)

  (*   | <{ !dst := src -> pc' }> => *)
  (*       fun ρ m => *)
  (*         I pc (ρ, m) -> *)
  (*         ∃ m', *)
  (*           set_at m (get_reg ρ dst) (get_reg ρ src) = Some m' *)
  (*           ∧ I pc' (ρ, m') *)

  (*   | <{ if cond then goto ifso else goto ifnot }> => *)
  (*       fun ρ m => *)
  (*         I pc (ρ, m) -> *)
  (*         if (get_reg ρ cond =? 0)%Z *)
  (*         then I ifso (ρ, m) *)
  (*         else I ifnot (ρ, m) *)

  (*   | <{ dst := @call sig args -> pc' }> => *)
  (*       fun ρ m => *)
  (*         I pc (ρ, m) -> *)
  (*         ∃ fn Pre Post, *)
  (*           find_fun P sig = Some fn *)
  (*           ∧ hoare P Pre fn Post *)
  (*           ∧ Pre (get_regs ρ args) m *)
  (*           ∧ ∀ v m', Post v m' -> I pc' (set_reg ρ dst v, m') *)
  (*  end. *)

  (* Compute fun I Q => Forall (check_pc_inv I Q) (map_to_list my_code). *)

  (* Definition wp_inv (f: function) (I: node_inv) (Q: postcondition) : *)
  (*   regmap -> memory -> Prop := *)
  (*   fun ρ m => *)
  (*     let code_list := map_to_list (fn_code f) in *)
  (*     let soundness_prop := fold_right *)
    
End WPGenerator.
