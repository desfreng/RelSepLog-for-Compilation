From RSL Require Import Prelude.

From RSL.Commons Require Export Language.

From RSL.RTL Require Export RTL Notations.

Import RTLNotations.

Inductive stackframe : Type :=
| Stackframe
    (res: reg) (* where to store the result *)
    (f: rtl_function) (* calling function *)
    (pc: node) (* program point in caller function *)
    (ρ: regbank) (* state in caller function *)
.

Inductive pcstate : Type :=
| State
    (f: rtl_function) (* current function *)
    (pc: node) (* current program point in c *)
    (ρ: regbank) (* register state *)

| CallState
    (f: rtl_function) (* function to call *)
    (args: list val) (* arguments to the call *)

| ReturnState
    (v: val). (* return value for the call *)

Definition rtl_state : Type := list stackframe * pcstate.

Variant rtl_step (P: rtl_program) : rtl_state * memory -> rtl_state * memory -> Prop :=
| exec_Inop: ∀ σ m ρ f pc pc',
  f@pc is <<{ nop -> pc' }>> ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ, m)

| exec_Iret: ∀ σ m ρ f pc r v,
  f@pc is <<{ ret r }>> ->
  ρ@r ⇒ v ->
  rtl_step P (σ, State f pc ρ, m) (σ, ReturnState v, m)

| exec_Iop: ∀ σ m ρ f pc op args dst pc' ρ' v vals,
  f@pc is <<{ dst := @op args -> pc' }>> ->
  ρ@args ⇒ vals ->
  eval_op op vals = Some v ->
  ⟦dst ⇐ v⟧ρ = ρ' ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ', m)

| exec_Iload: ∀ σ m ρ f pc dst src pc' ρ' addr v,
  f@pc is <<{ dst := !src -> pc' }>> ->
  ρ@src ⇒ addr ->
  get_at addr m = Some v ->
  ⟦dst ⇐ v⟧ρ = ρ' ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ', m)

| exec_Istore: ∀ σ m ρ f pc dst src pc' m' addr v,
  f@pc is <<{ !dst := src -> pc' }>> ->
  ρ@dst ⇒ addr ->
  ρ@src ⇒ v ->
  set_at addr v m = Some m' ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ, m')

| exec_Ialloc : ∀ σ m ρ f pc dst pc' ρ' m' l v,
  f@pc is <<{ dst := alloc () -> pc' }>> ->
  alloc_at l v m = Some m' ->
  ⟦dst ⇐ VPtr l⟧ρ = ρ' ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ', m')

| exec_Ifree : ∀ σ m ρ f pc src pc' m' addr,
  f@pc is <<{ free src -> pc' }>> ->
  ρ@src ⇒ addr ->
  free_at addr m = Some m' ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ, m')

| exec_Icond: ∀  σ m ρ f pc cond ifso ifnot v pc',
  f@pc is <<{ if cond then goto ifso else goto ifnot }>> ->
  ρ@cond ⇒ VBool v ->
  pc' = (if v then ifso else ifnot) ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ, m)

| exec_Icall: ∀ σ m ρ f pc dst sig args pc' σ' fn vals,
  f@pc is <<{ dst := @call sig args -> pc' }>> ->
  find_fun P sig = Some fn ->
  ρ@args ⇒ vals ->
  Stackframe dst f pc' ρ :: σ = σ' ->
  rtl_step P (σ, State f pc ρ, m) (σ', CallState fn vals, m)

| exec_function: ∀ σ m ρ f args,
  length args = length (rtl_fn_regs f) ->
  init_regs (rtl_fn_regs f) args = ρ ->
  rtl_step P (σ, CallState f args, m) (σ, State f (rtl_fn_entrypoint f) ρ, m)

| exec_return: ∀ σ m ρ f pc dst v ρ',
  ⟦dst ⇐ v⟧ρ = ρ' ->
  rtl_step P (Stackframe dst f pc ρ :: σ, ReturnState v, m) (σ, State f pc ρ', m)
.

Definition is_rtl_final (s: rtl_state) : option (val) :=
  match s with
  | ([], ReturnState v) => Some (v)
  | _ => None
  end.

Lemma rtl_final_no_step s v:
  is_rtl_final s = Some v ->
  ∀ m p s', ~rtl_step p (s, m) s'.
Proof.
  intros H ? ? ? Hstep.
  destruct s as [[] []]; inv H. inv Hstep.
Qed.

Lemma rtl_memory_mono p s m s' m':
  rtl_step p (s, m) (s', m') ->
  dom m ⊆ dom m'.
Proof.
  intros Hstep.
  inv Hstep as [ | | | | | ? ? ? ? ? ? ? ? ? ? ? ? Hm | | | | | ]; try done.
  - by erewrite update_at_dom.
  - apply alloc_at_dom in Hm as <-.
    by set_solver.
  - by erewrite update_at_dom.
Qed.

Lemma can_step_mono p s m t mm:
  rtl_step p (s, m) t ->
  ∃ t, rtl_step p (s, m ∪ mm) t.
Proof.
  intros H. inv H; try by do 2 econstructor.
  - eexists.
    eapply exec_Iload; try done.
    by apply get_at_mono.
  - eexists.
    eapply exec_Istore; try done.
    by apply update_at_mono.
  - destruct (can_alloc (m ∪ mm) inhabitant) as (l' & m'' & Hm).
    by do 2 econstructor.
  - eexists.
    eapply exec_Ifree; try done.
    by apply update_at_mono.
Qed.

Lemma rtl_mixin_lang : LangMixin rtl_step is_rtl_final.
Proof.
  constructor.
  - by apply rtl_final_no_step.
  - by eapply can_step_mono.
Qed.

Definition rtl_lang : lang := Lang _ _ _ _ _ rtl_mixin_lang.

Section SemProp.
  Let Λ : lang := rtl_lang.
  Context (P: prog Λ).
  Implicit Type s : config Λ.
  Implicit Type v : value Λ.

  (** Lemmas on the step relation  *)
  Lemma is_final_struct s v m :
    is_final s = Some (v, m) ->
    s = ([], ReturnState v, m).
  Proof using Type.
    intros H. destruct s as [[[] []] ?]; now inv H.
  Qed.

  Lemma ret_no_nsteps s v m : ∀ n t,
    is_final s = Some (v, m) ->
    P ⊨ s -{ n }> t ->
    t = ([], ReturnState v, m) ∧ n = 0.
  Proof using Type.
    intros n t Hfin H.
    apply is_final_struct in Hfin. subst.
    destruct n.
    - now inv H.
    - destruct (nsteps_inv_l _ _ _ H) as (y & Hstep & _).
      inv Hstep.
  Qed.

  Lemma ret_no_step s v m: ∀ t,
    is_final s = Some (v, m) ->
    P ⊨ s ->>* t ->
    t = ([], ReturnState v, m).
  Proof using Type.
    intros t Hfin H.
    destruct (rtc_nsteps_1 _ _ H) as [].
    eapply ret_no_nsteps; eassumption.
  Qed.

  (** Lift and Unlift lemmas for step *)
  Lemma lift_step σ σ' Σ ps pt m m':
    P ⊨ (σ, ps, m) ->> (σ', pt, m') ->
    P ⊨ (σ ++ Σ, ps, m) ->> (σ' ++ Σ, pt, m').
  Proof using Type.
    intros H; inv H; econstructor; now eauto.
  Qed.

  Lemma unlift_step σ ps m σ' pt m' Σ:
    P ⊨ (σ ++ Σ, ps, m) ->> (σ' ++ Σ, pt, m') ->
    P ⊨ (σ, ps, m) ->> (σ', pt, m').
  Proof using Type.
    intros H; inv H;
      rewrite ?app_comm_cons in *;
      eassert _ by (eapply app_inv_tail; eassumption);
      subst; econstructor; now eauto.
  Qed.

  Theorem lift_steps σ ps m σ' pt m' Σ:
    P ⊨ (σ, ps, m) ->>* (σ', pt, m') ->
    P ⊨ (σ ++ Σ, ps, m) ->>* (σ' ++ Σ, pt, m').
  Proof using Type.
    intros Hrtc.
    remember (σ, ps, m) as x eqn:Hx.
    remember (σ', pt, m') as y eqn:Hy.
    induction Hrtc as [ y | x y z H Hrtc IH]
      in σ, ps, m, Hx, σ', pt, m', Hy |- *.
    - subst. inv Hy. reflexivity.
    - subst. destruct y as [[] ?].
      etransitivity.
      + apply rtc_once. apply lift_step. eassumption.
      + eauto.
  Qed.

  Lemma ret_can_progress frame σ v m :
    can_progress P (frame :: σ, ReturnState v, m).
  Proof using Type. destruct frame. by do 2 econstructor. Qed.

  Lemma ret_empty_final v m:
    ~ can_progress P ([], ReturnState v, m).
  Proof using Type. intros [u H]. inv H. Qed.

  Lemma lift_can_progress σ Σ ps m:
    can_progress P (σ, ps, m) ->
    can_progress P (σ ++ Σ, ps, m).
  Proof using Type.
    intros [[[] ?] Ht]. eexists. apply lift_step. eassumption.
  Qed.

  Lemma unlift_can_progress σ Σ ps m:
    is_final ((σ, ps, m) : config Λ)= None ->
    can_progress P (σ ++ Σ, ps, m) ->
    can_progress P (σ, ps, m).
  Proof using Type.
    intros Hfin [[[] ?] Ht].
    inv Ht; try by do 2 econstructor.
    destruct σ as [|[]]; inv Hfin.
    econstructor. try by do 2 econstructor.
  Qed.

  Lemma step_frame_preserved σ Σ ps m t'' :
    is_final ((σ, ps, m) : config Λ) = None ->
    P ⊨ (σ ++ Σ, ps, m) ->> t'' ->
    ∃ σ' pt m', t'' = (σ' ++ Σ, pt, m') ∧ P ⊨ (σ, ps, m) ->> (σ', pt, m').
  Proof using Type.
    intros Hnf Hstep.
    destruct t'' as [[σ'' pt] m'].
    inv Hstep as [ | | | | | | | | | | ? ? ? ? ? ? ? ? ? Heq];
      try (eexists _, _, _; split; [ done | by econstructor]).
    - eexists (_ :: _), _, _. split.
      + done.
      + by econstructor.
    - destruct σ as [|[]]; inv Hnf.
      inv Heq.
      eexists _, _, _; split; [ done | by econstructor].
  Qed.

  Lemma unlift_stuck σ Σ ps m :
    stuck P (σ, ps, m) ->
    stuck P (σ ++ Σ, ps, m).
  Proof using Type.
    intros [Hfin Hcan].
    split.
    - destruct σ, Σ; simpl; auto.
    - intros Hprog. apply Hcan.
      by eapply unlift_can_progress.
  Qed.

  Lemma unlift_super_stuck σ Σ ps m :
    super_stuck P (σ, ps, m) ->
    super_stuck P (σ ++ Σ, ps, m).
  Proof using Type.
    intros [Hfin Hcan].
    split.
    - destruct σ, Σ; simpl; auto.
    - intros ? ? Hprog. eapply Hcan; first done.
      eapply unlift_can_progress; last done.
      unfold is_final. by rewrite Hfin.
  Qed.

  Lemma eval_op_same_args {I op valt vals vs}:
    Forall2 (same_val I) valt vals ->
    eval_op op vals = Some vs ->
    ∃ vt, eval_op op valt = Some vt ∧ same_val I vt vs.
  Proof using Type.
    intros Hsame Hop.
    destruct op;
      destruct vals as [|[] [|[] []]];
      try inv Hop as [H];
      try inv Hsame as [ | ? ? ? ? Hval1 Hsame'];
      try inv Hsame' as [ | ? ? ? ? Hval2 Hsame''];
      try inv Hsame'' as [ | ];
      try inv Hval1;
      try inv Hval2;
      try (eexists; split; done || by constructor).
    case_match eqn:Hcond.
    - congruence.
    - inv H. eexists. split; simpl.
      + by rewrite Hcond.
      + by constructor.
  Qed.
End SemProp.

(* Lemma unfold_call fn : ∀ n dst f pc ρ args m σ' σ t m', *)
(*   P ⊨ (Stackframe dst f pc ρ :: σ, CallState fn args, m) -{n}> (σ', t, m') -> *)
(*   (∃ σ'', *)
(*       σ = σ'' ++ Stackframe dst f pc ρ :: σ *)
(*       ∧ P ⊨ ([], CallState fn args, m) -{n}> (σ'', t, m')) *)
(*   ∨ *)
(*     (∃ m1 m2 v m'', *)
(*         n = 1 + m1 + m2 *)
(*         ∧ P ⊨ ([], CallState fn args, m) -{m1}> ([], ReturnState v, m'') *)
(*         ∧ P ⊨ ([], State f pc (⟦dst ⇐ v⟧ρ), m'') -{m2}> (σ, t, m') *)
(*     ). *)
(* Proof using Type. *)
(*   intros n. *)
(*   induction n as [ | n IH ]; *)
(*     intros dst f pc ρ args m σ t m' Hrtc. *)
(*   - inv Hrtc. left. exists []. split; auto. constructor. *)
(*   - apply nsteps_inv_r in Hrtc. destruct Hrtc as ([[] ?] & Hrtc & Hstep). *)
(*     apply IH in Hrtc. *)
(*     destruct Hrtc *)
(*       as [(σ' & -> & Hlift) | (m1 & m2 & v & m'' & Hn & Hcall & Hrest)]. *)
(*     + inv Hstep as [ | | | | | | | | ? ? ? ? ? ? v ? ? Hσ]; *)
(*         try (left; eexists; split; *)
(*              [ rewrite ? app_comm_cons; reflexivity *)
(*              | eapply nsteps_r; [ now apply Hlift | econstructor; now eauto] *)
(*              ] *)
(*           ). *)
(*       destruct σ'; inv Hσ. *)
(*       * right. exists n, 0, v, m'. repeat split; eauto. constructor. *)
(*       * left. eexists. split. *)
(*         -- reflexivity. *)
(*         -- eapply nsteps_r; [ now apply Hlift | econstructor; now eauto]. *)
(*     + inversion Hstep; subst; right; (exists m1, (S m2), v, m''); repeat split; *)
(*         now eauto || (eapply nsteps_r; *)
(*                       [ now apply Hrest | econstructor; now eauto]). *)
(* Qed. *)
