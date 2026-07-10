From RSL Require Import Prelude.
From RSL.Commons Require Import Language.

From stdpp Require Import gmap.

From RSL.RTL Require Import RTL Notations.

Import RTLNotations.

Inductive stackframe : Type :=
| Stackframe
    (res: reg) (* where to store the result *)
    (f: function) (* calling function *)
    (pc: node) (* program point in caller function *)
    (ρ: regbank) (* state in caller function *)
.

Inductive pcstate : Type :=
| State
    (f: function) (* current function *)
    (pc: node) (* current program point in c *)
    (ρ: regbank) (* register state *)

| CallState
    (f: function) (* function to call *)
    (args: list val) (* arguments to the call *)

| ReturnState
    (v: val). (* return value for the call *)

Definition rtl_state : Type := list stackframe * pcstate.

Inductive rtl_step (P: program) : rtl_state * memory -> rtl_state * memory -> Prop :=
| exec_Inop: ∀ σ m ρ f pc pc',
  f@pc is <<{ nop -> pc' }>> ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ, m)

| exec_Iret: forall σ m ρ f pc r v,
  f@pc is <<{ ret r }>> ->
  ρ@r ⇒ v ->
  rtl_step P (σ, State f pc ρ, m) (σ, ReturnState v, m)

| exec_Iop: forall σ m ρ f pc op args dst pc' ρ' v vals,
  f@pc is <<{ dst := @op args -> pc' }>> ->
  ρ@args ⇒ vals ->
  eval_op op vals = Some v ->
  ⟦dst ⇐ v⟧ρ = ρ' ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ', m)

| exec_Iload: forall σ m ρ f pc dst src pc' ρ' addr v,
  f@pc is <<{ dst := !src -> pc' }>> ->
  ρ@src ⇒ addr ->
  get_at addr m = Some v ->
  ⟦dst ⇐ v⟧ρ = ρ' ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ', m)

| exec_Istore: forall σ m ρ f pc dst src pc' m' addr v,
  f@pc is <<{ !dst := src -> pc' }>> ->
  ρ@dst ⇒ addr ->
  ρ@src ⇒ v ->
  set_at addr v m = Some m' ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ, m')

| exec_Icond: forall  σ m ρ f pc cond ifso ifnot v pc',
  f@pc is <<{ if cond then goto ifso else goto ifnot }>> ->
  ρ@cond ⇒ v ->
  pc' = (if Z.eqb v 0 then ifso else ifnot) ->
  rtl_step P (σ, State f pc ρ, m) (σ, State f pc' ρ, m)

| exec_Icall: forall σ m ρ f pc dst sig args pc' σ' fn vals,
  f@pc is <<{ dst := @call sig args -> pc' }>> ->
  find_fun P sig = Some fn ->
  ρ@args ⇒ vals ->
  Stackframe dst f pc' ρ :: σ = σ' ->
  rtl_step P (σ, State f pc ρ, m) (σ', CallState fn vals, m)

| exec_function: forall σ m ρ f args,
  length args = length (fn_regs f) ->
  ρ@(fn_regs f) ⇒ args ->
  rtl_step P (σ, CallState f args, m) (σ, State f (fn_entrypoint f) ρ, m)

| exec_return: forall σ m ρ f pc dst v ρ',
  ⟦dst ⇐ v⟧ρ = ρ' ->
  rtl_step P (Stackframe dst f pc ρ :: σ, ReturnState v, m) (σ, State f pc ρ', m)
.

Definition is_final (s: rtl_state * memory) : option (val * memory) :=
  match s with
  | ([], ReturnState v, m) => Some (v, m)
  | _ => None
  end.

Lemma rtl_mixin_lang : LangMixin rtl_step is_final.
Proof.
  constructor. intros [[[] []] ?] ? ? H ? ? Hstep; inv H. inv Hstep.
Qed.

Definition rtl_lang : lang := Lang _ _ _ _ _ rtl_mixin_lang.

Section SemProp.
  Let Λ : lang := rtl_lang.
  Context (P: prog Λ).

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
  Lemma lift_step : ∀ σ σ' Σ s t m m',
    P ⊨ (σ, s, m) ->> (σ', t, m') ->
    P ⊨ (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m').
  Proof using Type.
    intros ? ? ? ? ? ? ? H; inv H; econstructor; now eauto.
  Qed.

  Lemma unlift_step : ∀ σ s m σ' t m' Σ,
    P ⊨ (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m') ->
    P ⊨ (σ, s, m) ->> (σ', t, m').
  Proof using Type.
    intros ? ? ? ? ? ? ? H; inv H;
      rewrite ? app_comm_cons in *;
      eassert _ by (eapply app_inv_tail; eassumption);
      subst; econstructor; now eauto.
  Qed.

  Theorem lift_steps : ∀ σ s m σ' t m' Σ,
    P ⊨ (σ, s, m) ->>* (σ', t, m') ->
    P ⊨ (σ ++ Σ, s, m) ->>* (σ' ++ Σ, t, m').
  Proof using Type.
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

  Lemma unfold_call fn : ∀ n dst f pc ρ args m σ t m',
    P ⊨ ([Stackframe dst f pc ρ], CallState fn args, m) -{n}> (σ, t, m') ->
    (∃ σ',
        σ = σ' ++ [Stackframe dst f pc ρ]
        ∧ P ⊨ ([], CallState fn args, m) -{n}> (σ', t, m'))
    ∨
      (∃ m1 m2 v m'',
          n = 1 + m1 + m2
          ∧ P ⊨ ([], CallState fn args, m) -{m1}> ([], ReturnState v, m'')
          ∧ P ⊨ ([], State f pc (⟦dst ⇐ v⟧ρ), m'') -{m2}> (σ, t, m')
      ).
  Proof using Type.
    intros n.
    induction n as [ | n IH ];
      intros dst f pc ρ args m σ t m' Hrtc.
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
  Proof using Type. intros []. repeat econstructor; now eauto. Qed.

  Lemma ret_stuck_in_empty : ∀ v m,
    ~ can_progress P ([], ReturnState v, m).
  Proof using Type. intros v m [u H]. inv H. Qed.

  Lemma lift_not_stuck : ∀ σ Σ s m,
    can_progress P (σ, s, m) ->
    can_progress P (σ ++ Σ, s, m).
  Proof using Type. intros σ Σ s m [[[] ?] Ht]. eexists. apply lift_step. eassumption. Qed.

End SemProp.
