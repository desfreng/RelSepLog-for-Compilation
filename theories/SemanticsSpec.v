From stdpp Require Import prelude.
From stdpp Require Import gmap.

From RSL Require Import RTL.
From RSL Require Import Notations.
From RSL Require Import Semantics.
From RSL Require Import Logic.

Import RTLNotations.

(* Set Mangle Names. *)

Section StepLemmas.
  (** Lemmas on the step relation  *)

  Lemma nsteps_inv_l {A : Type} {R : relation A} :
    ∀ n x z, nsteps R (S n) x z → ∃ y : A, R x y ∧ nsteps R n y z.
  Proof. intros n x z H; inv H; eexists; eauto. Qed.

  Lemma ret_no_nsteps P : ∀ n v m t,
    P ⊨ ([], ReturnState v, m) -{n}> t ->
    t = ([], ReturnState v, m) ∧ n = 0.
  Proof.
    intros [] v m t H.
    - now inv H.
    - destruct (nsteps_inv_l _ _ _ H) as (y & Hstep & _).
      inv Hstep.
  Qed.

  Lemma ret_no_step P : ∀ v m t,
    P ⊨ ([], ReturnState v, m) ->>* t ->
    t = ([], ReturnState v, m).
  Proof.
    intros v m t H.
    destruct (rtc_nsteps_1 _ _ H) as []. eapply ret_no_nsteps. eassumption.
  Qed.

  (** Lift and Unlift lemmas for step *)
  Lemma lift_step P : ∀ σ s m σ' t m' Σ,
    P ⊨ (σ, s, m) ->> (σ', t, m') ->
    P ⊨ (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m').
  Proof.
    intros ? ? ? ? ? ? ? H; inv H; econstructor; now eauto.
  Qed.

  Lemma unlift_step P : ∀ σ s m σ' t m' Σ,
    P ⊨ (σ ++ Σ, s, m) ->> (σ' ++ Σ, t, m') ->
    P ⊨ (σ, s, m) ->> (σ', t, m').
  Proof.
    intros ? ? ? ? ? ? ? H; inv H;
      rewrite ? app_comm_cons in *;
      eassert _ by (eapply app_inv_tail; eassumption);
      subst; econstructor; now eauto.
  Qed.

  Theorem lift_steps P : ∀ σ s m σ' t m' Σ,
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
End StepLemmas.

(** Call unfolding  *)

Section CallUnfold.

  Lemma unfold_call P fn : ∀ n res f pc ρ args m σ t m',
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
End CallUnfold.

Section Registers.
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
End Registers.

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
  simpl_reg by repeat (f_equal || lia || unfold_Prop || split).

Section StatesClassification.
  Definition is_final (s: state) : option (val * memory) :=
    match s with
    | ([], ReturnState v, m) => Some (v, m)
    | _ => None
    end.

  Lemma is_final_extract : ∀ s v m,
    is_final s = Some (v, m) ->
    s = ([], ReturnState v, m).
  Proof. intros [[[] []] ?] ? ?; simpl; intros H; now inv H. Qed.

  Lemma final_is_final : ∀ s,
    final s <-> ∃ v m, is_final s = Some (v, m).
  Proof.
    intros [[[] []] ?]; split; intros (? & ? & H) || intro H;
      inv H; repeat econstructor.
  Qed.

  Lemma final_to_final : ∀ s v m,
    is_final s = Some (v, m) -> final s.
  Proof.
    intros [[[] []] ?] ? ? H; inv H; repeat econstructor.
  Qed.

  Lemma final_no_progress : ∀ s P,
    final s -> ~ can_progress P s.
  Proof.
    intros s P Hfin [t Hstep]. inv Hfin. inv Hstep.
  Qed.

  Lemma final_not_stuck : ∀ s P,
    final s -> ~ stuck P s.
  Proof.
    intros s P Hfin [Hnprogress Hnfin]. tauto.
  Qed.

  Lemma progress_not_stuck : ∀ s P,
    can_progress P s -> ~ stuck P s.
  Proof.
    intros s P Hfin [Hnprogress Hnfin]. tauto.
  Qed.

  Lemma ret_not_stuck : ∀ P frame σ v m,
    can_progress P (frame :: σ, ReturnState v, m).
  Proof. intros P []. repeat econstructor; now eauto. Qed.

  Lemma ret_stuck_in_empty : ∀ P v m,
    ~ can_progress P ([], ReturnState v, m).
  Proof. intros P v m [u H]. inv H. Qed.

  Lemma lift_not_stuck : ∀ P σ Σ s m,
    can_progress P (σ, s, m) ->
    can_progress P (σ ++ Σ, s, m).
  Proof. intros P σ Σ s m [[[] ?] Ht]. eexists. apply lift_step. eassumption. Qed.

End StatesClassification.
