From RSL Require Import Prelude.

From stdpp Require Import gmap.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Notations.

Import RTLNotations.

(* Set Mangle Names. *)

Fixpoint init_regs (vl: list val) (rl: list reg) : regmap :=
  match rl, vl with
  | r :: rs, v :: vs => <[r := v]>(init_regs vs rs)
  | _, _ => ∅
  end.

Inductive stackframe : Type :=
| Stackframe
    (res: reg) (* where to store the result *)
    (f: function) (* calling function *)
    (pc: node) (* program point in caller function *)
    (ρ: regmap) (* state in caller function *)
.

Inductive pcstate : Type :=
| State
    (f: function) (* current function *)
    (pc: node) (* current program point in c *)
    (ρ: regmap) (* register state *)

| CallState
    (f: function) (* function to call *)
    (args: list val) (* arguments to the call *)

| ReturnState
    (v: val). (* return value for the call *)

Definition rtl_state : Type := list stackframe * pcstate * memory.

Inductive rtl_step (P: program) : rtl_state -> rtl_state -> Prop :=
| exec_Inop: ∀ σ m ρ f pc pc',
  f@pc is <{ nop -> pc' }> ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ, m)

| exec_Iret: forall σ m ρ f pc r v,
  f@pc is <{ ret r }> ->
  get_reg r ρ = v ->
  rtl_step P (σ, State f pc ρ, m) (σ, ReturnState v, m)

| exec_Iop: forall σ m ρ f pc op args dst pc' ρ' v,
  f@pc is <{ dst := @op args -> pc' }> ->
  eval_op op (get_regs args ρ) = Some v ->
  set_reg dst v ρ = ρ' ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ', m)

| exec_Iload: forall σ m ρ f pc dst src pc' ρ' addr v,
  f@pc is <{ dst := !src -> pc' }> ->
  get_reg src ρ = addr ->
  get_at addr m = Some v ->
  set_reg dst v ρ = ρ' ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ', m)

| exec_Istore: forall σ m ρ f pc dst src pc' m' addr v,
  f@pc is <{ !dst := src -> pc' }> ->
  get_reg dst ρ = addr ->
  get_reg src ρ = v ->
  set_at addr v m = Some m' ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ, m')

| exec_Icond: forall  σ m ρ f pc cond ifso ifnot v pc',
  f@pc is <{ if cond then goto ifso else goto ifnot }> ->
  get_reg cond ρ = v ->
  pc' = (if Z.eqb v 0 then ifso else ifnot) ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ, m)

| exec_Icall: forall σ m ρ f pc dst sig args pc' σ' fn,
  f@pc is <{ dst := @call sig args -> pc' }> ->
  find_fun P sig = Some fn ->
  Stackframe dst f pc' ρ :: σ = σ' ->
  rtl_step P (σ, State f pc ρ, m) (σ', CallState fn (get_regs args ρ), m)

| exec_function: forall σ m ρ f args,
  length args = length (fn_regs f) ->
  init_regs args (fn_regs f) = ρ ->
  rtl_step P (σ, CallState f args, m) (σ, State f (fn_entrypoint f) ρ, m)

| exec_return: forall σ m ρ f pc dst v ρ',
  set_reg dst v ρ = ρ' ->
  rtl_step P (Stackframe dst f pc ρ :: σ, ReturnState v, m) (σ, State f pc ρ', m)
.

Definition is_final (s: rtl_state) : option (val * memory) :=
  match s with
  | ([], ReturnState v, m) => Some (v, m)
  | _ => None
  end.

Lemma rtl_mixin_lang : LangMixin rtl_step is_final.
Proof.
  constructor. intros ? [[[] []] ?] ? ? H Hstep; inv H. inv Hstep.
Qed.

Definition rtl_lang : lang := Lang _ _ _ _ _ rtl_mixin_lang.

Instance stackframe_eq_dec : EqDecision stackframe.
Proof.
  unfold EqDecision, Decision.
  decide equality; apply (decide _).
Qed.

Instance pcstate_eq_dec : EqDecision pcstate.
Proof.
  unfold EqDecision, Decision.
  decide equality; apply (decide _).
Qed.

Instance rtl_state_eqdec : EqDecision rtl_state.
Proof.
  unfold EqDecision, Decision.
  decide equality.
  - apply (decide _).
  - decide equality; apply (decide _).
Qed.

Definition exec_step (P: program) (s: rtl_state) : option rtl_state :=
  match s with
  | (σ, State f pc ρ, m) =>
      match fn_code f !! pc with
      | Some <{ nop -> pc' }> =>
          Some (σ, State f pc' ρ, m)
      | Some <{ ret r }> =>
          Some (σ, ReturnState (get_reg r ρ), m)
      | Some <{ dst := @op args -> pc' }> =>
          match eval_op op (get_regs args ρ) with
          | Some v => Some (σ, State f pc' (set_reg dst v ρ), m)
          | None => None
          end
      | Some <{ dst := !src -> pc' }> =>
          match get_at (get_reg src ρ) m with
          | Some v => Some (σ, State f pc' (set_reg dst v ρ), m)
          | None => None
          end
      | Some <{ !dst := src -> pc' }> =>
          match set_at (get_reg dst ρ) (get_reg src ρ) m with
          | Some m' => Some (σ, State f pc' ρ, m')
          | None => None
          end
      | Some <{ if cond then goto ifso else goto ifnot }> =>
          let v := get_reg cond ρ in
          let pc' := if Z.eqb v 0 then ifso else ifnot in
          Some (σ, State f pc' ρ, m)
      | Some <{ dst := @call sig args -> pc' }> =>
          match find_fun P sig with
          | Some fn => Some (Stackframe dst f pc' ρ :: σ, CallState fn (get_regs args ρ), m)
          | None => None
          end
      | _ => None
      end
  | (σ, CallState f args, m) =>
      if decide (length args = length (fn_regs f)) then
        Some (σ, State f (fn_entrypoint f) (init_regs args (fn_regs f)), m)
      else None
  | (Stackframe dst f pc ρ :: σ, ReturnState v, m) =>
      Some (σ, State f pc (set_reg dst v ρ), m)
  | _ => None
  end.

Lemma exec_step_sound P s t :
  exec_step P s = Some t -> rtl_step P s t.
Proof.
  unfold exec_step. intro H.
  now repeat (case_match; try (inv H; try (econstructor; now eauto))).
Qed.

Section SemProp.
  Let Λ : lang := rtl_lang.
  Context (P: prog Λ).

  (** Lemmas on the step relation  *)
  Lemma is_final_struct : ∀ v m s,
    is_final s = Some (v, m) ->
    s = ([], ReturnState v, m).
  Proof. intros v m [[[] []] ?] H; now inv H. Qed.

  Lemma ret_no_nsteps : ∀ n v m s t,
    is_final s = Some (v, m) ->
    P ⊨ s -{ n }> t ->
    t = ([], ReturnState v, m) ∧ n = 0.
  Proof.
    intros n v m s t Hfin H.
    apply is_final_struct in Hfin. subst.
    destruct n.
    - now inv H.
    - destruct (nsteps_inv_l _ _ _ H) as (y & Hstep & _).
      inv Hstep.
  Qed.

  Lemma ret_no_step : ∀ v m s t,
    is_final s = Some (v, m) ->
    P ⊨ s ->>* t ->
    t = ([], ReturnState v, m).
  Proof.
    intros v m s t Hfin H.
    destruct (rtc_nsteps_1 _ _ H) as [].
    eapply ret_no_nsteps; eassumption.
  Qed.

  (** Lift and Unlift lemmas for step *)
  Lemma lift_step : ∀ σ σ' Σ s t m m',
    P ⊨ (σ, s, m) ->> (σ', t, m') ->
    P ⊨ (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m').
  Proof.
    intros ? ? ? ? ? ? ? H; inv H; econstructor; now eauto.
  Qed.

  Lemma unlift_step : ∀ σ s m σ' t m' Σ,
    P ⊨ (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m') ->
    P ⊨ (σ, s, m) ->> (σ', t, m').
  Proof.
    intros ? ? ? ? ? ? ? H; inv H;
      rewrite ? app_comm_cons in *;
      eassert _ by (eapply app_inv_tail; eassumption);
      subst; econstructor; now eauto.
  Qed.

  Theorem lift_steps : ∀ σ s m σ' t m' Σ,
    P ⊨ (σ, s, m) ->>* (σ', t, m') ->
    P ⊨ (σ ++ Σ, s, m) ->>* (σ' ++ Σ, t, m').
  Proof.
    intros σ s m σ' t m' Σ Hrtc.
    remember (σ, s, m) as x eqn:Hx.
    remember (σ', t, m') as y eqn:Hy.
    induction Hrtc as [ y | x y z H Hrtc IH]
      in σ, s, m, Hx, σ', t, m', Hy |- *.
    - subst. inv Hy. reflexivity.
    - subst. destruct y as [[] ?].
      etransitivity.
      + apply rtc_once. apply lift_step. eassumption.
      + eauto.
  Qed.

  Lemma unfold_call fn : ∀ n res f pc ρ args m σ t m',
    P ⊨ ([Stackframe res f pc ρ], CallState fn args, m) -{n}> (σ, t, m') ->
    (∃ σ',
        σ = σ' ++ [Stackframe res f pc ρ]
        ∧ P ⊨ ([], CallState fn args, m) -{n}> (σ', t, m'))
    ∨
      (∃ m1 m2 v m'',
          n = 1 + m1 + m2
          ∧ P ⊨ ([], CallState fn args, m) -{m1}> ([], ReturnState v, m'')
          ∧ P ⊨ ([], State f pc (set_reg res v ρ), m'') -{m2}> (σ, t, m')
      ).
  Proof.
    intros n.
    induction n as [ | n IH ];
      intros res f pc ρ args m σ t m' Hrtc.
    - inv Hrtc. left. exists []. split; auto. constructor.
    - apply nsteps_inv_r in Hrtc. destruct Hrtc as ([[] ?] & Hrtc & Hstep).
      apply IH in Hrtc.
      destruct Hrtc
        as [(σ' & -> & Hlift) | (m1 & m2 & v & m'' & Hn & Hcall & Hrest)].
      + inv Hstep as [ | | | | | | | | ? ? ? ? ? ? v ? ? Hσ];
          try (left; eexists; split;
               [ rewrite ? app_comm_cons; reflexivity
               | eapply nsteps_r; [ now apply Hlift | econstructor; now eauto]
               ]
            ).
        destruct σ'; inv Hσ.
        * right. exists n, 0, v, m'. repeat split; eauto. constructor.
        * left. eexists. split.
          -- reflexivity.
          -- eapply nsteps_r; [ now apply Hlift | econstructor; now eauto].
      + inversion Hstep; subst; right; (exists m1, (S m2), v, m''); repeat split;
          now eauto || (eapply nsteps_r;
                        [ now apply Hrest | econstructor; now eauto]).
  Qed.

  Lemma ret_not_stuck : ∀ frame σ v m,
    can_progress P (frame :: σ, ReturnState v, m).
  Proof. intros []. repeat econstructor; now eauto. Qed.

  Lemma ret_stuck_in_empty : ∀ v m,
    ~ can_progress P ([], ReturnState v, m).
  Proof. intros v m [u H]. inv H. Qed.

  Lemma lift_not_stuck : ∀ σ Σ s m,
    can_progress P (σ, s, m) ->
    can_progress P (σ ++ Σ, s, m).
  Proof. intros σ Σ s m [[[] ?] Ht]. eexists. apply lift_step. eassumption. Qed.

End SemProp.

Section Regs.
  Lemma get_regs_insert : ∀ regs r v ρ,
    r ∉ regs ->
    get_regs regs (<[r := v]> ρ) = get_regs regs ρ.
  Proof.
    intros regs r v ρ.
    induction regs as [|r' regs' IH]; intros Hnotin; [reflexivity |].
    simpl. f_equal.
    - unfold get_reg. rewrite (lookup_insert_ne ρ); set_solver.
    - apply IH. set_solver.
  Qed.

  Lemma get_regs_init_regs : ∀ regs args,
    NoDup regs ->
    length args = length regs ->
    get_regs regs (init_regs args regs) = args.
  Proof.
    intros regs args Hnodup.
    revert args.
    induction Hnodup as [|r regs Hnotin Hnodup IH]; intros args Hlen.
    - destruct args; [reflexivity | discriminate Hlen].
    - destruct args as [|v args]; [discriminate Hlen |].
      simpl in Hlen. injection Hlen as Hlen'.
      simpl. f_equal.
      + unfold get_reg. now rewrite (lookup_insert_eq (init_regs args regs)).
      + rewrite get_regs_insert by exact Hnotin.
        apply IH. exact Hlen'.
  Qed.

  Lemma get_reg_set_reg_eq : ∀ r v ρ,
    get_reg r (set_reg r v ρ) = v.
  Proof.
    intros r v ρ.
    unfold get_reg, set_reg.
    now rewrite (lookup_insert_eq ρ).
  Qed.

  Lemma get_reg_set_reg_neq : ∀ r r' v ρ,
    r ≠ r' -> get_reg r (set_reg r' v ρ) = get_reg r ρ.
  Proof.
    intros r r' v ρ Hneq.
    unfold get_reg, set_reg.
    now rewrite (lookup_insert_ne ρ).
  Qed.
End Regs.

Tactic Notation "simpl_reg" "by" tactic3(tac) :=
  repeat match goal with
    | _ => progress tac
    | |- context[get_reg _ (set_reg _ _ _)] =>
        (rewrite get_reg_set_reg_neq by tac)
        || (rewrite get_reg_set_reg_eq by tac)
    | H: get_reg ?r ?rho = _ |- context[get_reg ?r ?rho] =>
        repeat rewrite H
    end.

Global Tactic Notation "simpl_reg" :=
  simpl_reg by repeat (f_equal || lia ||split).

Section Succ.
  Let Λ : lang := rtl_lang.
  Context (P: prog Λ).

  Definition next (f: function) (pc: node) : list node :=
    match fn_code f !! pc with
    | Some (Inop succ) => [succ]
    | Some (Iop _ _ _ succ) => [succ]
    | Some (Iload _ _ succ) => [succ]
    | Some (Istore _ _ succ) => [succ]
    | Some (Icall _ _ _ succ) => [succ]
    | Some (Icond _ ifso ifnot) => [ifso; ifnot]
    | Some (Ireturn _) => []
    | None => []
    end.

  Lemma next_correct f pc : ∀ ρ ρ' m m' pc',
    P ⊨ ([], State f pc ρ, m) ->> ([], State f pc' ρ', m') ->
    pc' ∈ next f pc.
  Proof using Type.
    unfold next.
    intros ρ ρ' m m' pc' H.
    destruct (fn_code f !! pc) as [[] | ] eqn:Hi;
      inv H; try now constructor.
    case_match; do 2 constructor.
  Qed.
End Succ.
