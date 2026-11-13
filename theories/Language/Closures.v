From RSL Require Import Prelude.

From RSL.Language Require Import LanguageDef.

Section Clos.
  Context {Λ: lang} (g: genv Λ).

  (** NSteps : Exactly n steps *)

  Inductive nsteps : nat -> config Λ -> config Λ -> Prop :=
  | NStepsO :
    ∀ c, nsteps 0 c c
  | NStepsS :
    ∀ n c1 c2 c3,
    step g c1 c2 ->
    nsteps n c2 c3 ->
    nsteps (S n) c1 c3.

  Lemma nsteps_refl c : nsteps 0 c c.
  Proof using Type. by apply NStepsO. Qed.

  Lemma nsteps_one c1 c2 :
    step g c1 c2 -> nsteps 1 c1 c2.
  Proof using Type.
    intros H. eapply NStepsS.
    - done.
    - apply nsteps_refl.
  Qed.

  Lemma nsteps_trans n1 n2 c1 c2 c3 n :
    nsteps n1 c1 c2 ->
    nsteps n2 c2 c3 ->
    n = n1 + n2 ->
    nsteps n c1 c3.
  Proof using Type.
    intros H12 H24 ->.
    revert n2 c3 H24.
    induction H12 as [ c1 | n1 c1 c2 c3 H12 H23 IH ].
    - intros n2 c2. done.
    - intros n2 c4 H34.
      eapply NStepsS.
      + done.
      + by apply IH.
  Qed.

  Lemma nsteps_l n c1 c2 c3 :
    step g c1 c2 -> nsteps n c2 c3 -> nsteps (S n) c1 c3.
  Proof using Type. by apply NStepsS. Qed.

  Lemma nsteps_r n c1 c2 c3 :
    nsteps n c1 c2 -> step g c2 c3 -> nsteps (S n) c1 c3.
  Proof using Type.
    intros H12 H23.
    eapply nsteps_trans.
    - done.
    - by apply nsteps_one.
    - by rewrite Nat.add_1_r.
  Qed.

  Lemma nsteps_inv_l n c1 c3 :
    nsteps (S n) c1 c3 ->
    ∃ c2, step g c1 c2 ∧ nsteps n c2 c3.
  Proof using Type.
    intros H. inv H. by eexists.
  Qed.

  Lemma nsteps_inv_r n c1 c3:
    nsteps (S n) c1 c3 ->
    ∃ c2, nsteps n c1 c2 ∧ step g c2 c3.
  Proof using Type.
    intros H.
    remember (S n) as m eqn:Hm.
    induction H as [ | n' c1 c2 c4 Hstep H IH ] in n, Hm |- *; inv Hm.
    destruct n as [ | n ].
    - inv H. exists c1. split_and!.
      + by constructor.
      + done.
    - specialize (IH _ eq_refl) as (c3 & Hsteps & Hstep').
      exists c3. split_and!.
      + by econstructor.
      + done.
  Qed.

  Lemma nsteps_ind_l (P : nat -> config Λ -> config Λ -> Prop) :
    (∀ c, P 0 c c) ->
    (∀ n c1 c2 c3,
       step g c1 c2 -> nsteps n c2 c3 -> P n c2 c3 -> P (S n) c1 c3) ->
    ∀ n c1 c2, nsteps n c1 c2 -> P n c1 c2.
  Proof using Type. by apply nsteps_ind. Qed.

  Lemma nsteps_ind_r (P : nat -> config Λ -> config Λ -> Prop) :
    (∀ c, P 0 c c) ->
    (∀ n c1 c2 c3,
       nsteps n c1 c2 -> P n c1 c2 -> step g c2 c3 -> P (S n) c1 c3) ->
    ∀ n c1 c2, nsteps n c1 c2 -> P n c1 c2.
  Proof using Type.
    intros Hinit HstepR.
    assert (∀ n2 c2 c3,
              nsteps n2 c2 c3 ->
              ∀ n1 c1,
              nsteps n1 c1 c2 -> P n1 c1 c2 ->
              ∀ n,
              n = n1 + n2 -> P n c1 c3) as H.
    {
      induction 1 as [ c2 | n2 c2 c3 c4 H23 H34 IH ].
      - intros n1 c1 H12 HP ? ->. by rewrite Nat.add_0_r.
      - intros n1 c1 H12 HP ? ->.
        eapply IH.
        + by eapply nsteps_r.
        + by eapply HstepR.
        + lia.
    }
    intros n1 c1 c2 H12.
    eapply H.
    - done.
    - by apply nsteps_refl.
    - by apply Hinit.
    - done.
  Qed.


  (** Steps : Reflexive Transive Closure of step *)

  Inductive steps : config Λ -> config Λ -> Prop :=
  | StepsRefl :
    ∀ c, steps c c
  | StepsL :
    ∀ c1 c2 c3,
    step g c1 c2 ->
    steps c2 c3 ->
    steps c1 c3.

  Lemma steps_refl c : steps c c.
  Proof using Type. by constructor. Qed.

  Lemma steps_one c1 c2 :
    step g c1 c2 -> steps c1 c2.
  Proof using Type.
    intros H. eapply StepsL; by eauto using steps_refl.
  Qed.

  Lemma steps_trans c1 c2 c3 :
    steps c1 c2 -> steps c2 c3 -> steps c1 c3.
  Proof using Type.
    intros H12 H23.
    revert c3 H23.
    induction H12 as [ c1 | c1 c2 c3 H12 H23 IH ].
    - done.
    - intros. by eauto using StepsL.
  Qed.

  Lemma steps_l c1 c2 c3 :
    step g c1 c2 -> steps c2 c3 -> steps c1 c3.
  Proof using Type. by eapply StepsL. Qed.

  Lemma steps_r c1 c2 c3 :
    steps c1 c2 -> step g c2 c3 -> steps c1 c3.
  Proof using Type.
    intros H ?. eapply steps_trans; by eauto using steps_one.
  Qed.

  Lemma steps_inv_l c1 c3:
    steps c1 c3 ->
    (c1 = c3) ∨ (∃ c2, step g c1 c2 ∧ steps c2 c3).
  Proof using Type.
    intros H. inv H.
    - by left.
    - right. by eexists.
  Qed.

  Lemma steps_inv_r c1 c3:
    steps c1 c3 ->
    (c1 = c3) ∨ (∃ c2, steps c1 c2 ∧ step g c2 c3).
  Proof using Type.
    intros H. induction H as [ c | c1 c2 c3 H12 H23 IH ].
    - by left.
    - right. destruct IH as [-> | (? & ? & ?)].
      + eexists. split_and!; by eauto using steps_refl.
      + eexists; split_and!.
        * eapply steps_trans; eauto using steps_one.
        * done.
  Qed.

  Lemma steps_ind_l (P : config Λ -> config Λ -> Prop) :
    (∀ c, P c c) ->
    (∀ c1 c2 c3,
       step g c1 c2 -> steps c2 c3 -> P c2 c3 -> P c1 c3) ->
    ∀ c1 c2, steps c1 c2 -> P c1 c2.
  Proof using Type. by apply steps_ind. Qed.

  Lemma steps_ind_r (P : config Λ -> config Λ -> Prop) :
    (∀ c, P c c) ->
    (∀ c1 c2 c3,
       steps c1 c2 -> P c1 c2 -> step g c2 c3 -> P c1 c3) ->
    ∀ c1 c2, steps c1 c2 -> P c1 c2.
  Proof using Type.
    intros Hinit Hstep.
    assert (∀ c2 c3, steps c2 c3 -> ∀ c1, steps c1 c2 -> P c1 c2 -> P c1 c3) as H.
    {
      induction 1 as [ c2 | c2 c3 c4 H23 H34 IH ].
      - by intros.
      - intros. eapply IH.
        + by eapply steps_r.
        + by eapply Hstep.
    }
    intros c1 c2 H12.
    eapply H; eauto using steps_refl.
  Qed.

  Lemma steps_to_nsteps c1 c2 :
    steps c1 c2 -> ∃ n, nsteps n c1 c2.
  Proof using Type.
    intros H.
    induction H as [ c | c1 c2 c3 H12 _ (n & IH) ].
    - exists 0. by constructor.
    - exists (S n). by econstructor.
  Qed.

  Lemma nsteps_to_steps c1 c2 n :
    nsteps n c1 c2 -> steps c1 c2.
  Proof using Type.
    intros H. induction H as [ c | n c1 c2 c3 H12 _ IH ]; by econstructor.
  Qed.

  (** PSteps : at least one step *)

  Variant psteps : config Λ -> config Λ -> Prop :=
  | PStepsL : ∀ c1 c2 c3, step g c1 c2 -> steps c2 c3 -> psteps c1 c3.

  Lemma psteps_one c1 c2 :
    step g c1 c2 -> psteps c1 c2.
  Proof using Type. intros H. econstructor; eauto using steps_refl. Qed.

  Lemma psteps_to_steps c1 c2 : psteps c1 c2 -> steps c1 c2.
  Proof using Type. intros []. by econstructor. Qed.

  Lemma psteps_trans c1 c2 c3 :
    psteps c1 c2 -> psteps c2 c3 -> psteps c1 c3.
  Proof using Type.
    intros H1 H2. inv H1.
    econstructor.
    - done.
    - eapply steps_trans; by eauto using psteps_to_steps.
  Qed.

  Lemma psteps_l c1 c2 c3 :
    step g c1 c2 -> psteps c2 c3 -> psteps c1 c3.
  Proof using Type. intros. by econstructor; eauto using psteps_to_steps. Qed.

  Lemma psteps_r c1 c2 c3 :
    psteps c1 c2 -> step g c2 c3 -> psteps c1 c3.
  Proof using Type.
    intros [] ?. by econstructor; eauto using steps_r.
  Qed.

  Lemma psteps_inv_l c1 c3:
    psteps c1 c3 -> ∃ c2, step g c1 c2 ∧ steps c2 c3.
  Proof using Type.
    intros []. by eexists.
  Qed.

  Lemma psteps_inv_r c1 c3:
    psteps c1 c3 -> ∃ c2, steps c1 c2 ∧ step g c2 c3.
  Proof using Type.
    intros H. inv H as [ ? ? ? Hstep Hsteps%steps_inv_r].
    destruct Hsteps as [-> | (? & ? & ?)].
    - eexists; split_and!; by eauto using steps_refl.
    - eexists; split_and!.
      + by eapply steps_trans; eauto using steps_one.
      + done.
  Qed.

  Lemma psteps_steps_l c1 c2 c3 :
    steps c1 c2 -> psteps c2 c3 -> psteps c1 c3.
  Proof using Type.
    intros [-> | (? & ? & ?)]%steps_inv_l H2.
    - done.
    - econstructor.
      + done.
      + by eauto using steps_trans, psteps_to_steps.
  Qed.

  Lemma psteps_steps_r c1 c2 c3 :
    psteps c1 c2 -> steps c2 c3 -> psteps c1 c3.
  Proof using Type.
    intros H1 H2. inv H1.
    econstructor.
    - done.
    - by eapply steps_trans.
  Qed.

  Lemma steps_inv_psteps c1 c2 :
    steps c1 c2 -> c1 = c2 ∨ psteps c1 c2.
  Proof using Type.
    intros [-> | (? & ? & ?)]%steps_inv_l.
    - by left.
    - right. by econstructor.
  Qed.

  Lemma psteps_to_nsteps c1 c2 :
    psteps c1 c2 -> ∃ n, nsteps n c1 c2 ∧ n > 0.
  Proof using Type.
    intros [ ? ? ? Hstep Hsteps ].
    apply steps_to_nsteps in Hsteps as [n Hsteps].
    exists (S n). split.
    - by econstructor.
    - lia.
  Qed.

  Lemma nsteps_to_psteps c1 c2 n :
    nsteps n c1 c2 -> n > 0 -> psteps c1 c2.
  Proof using Type.
    intros H Hlt. destruct n.
    - inv Hlt.
    - apply nsteps_inv_l in H as (? & Hstep & Hsteps).
      by econstructor; eauto using nsteps_to_steps.
  Qed.

  Lemma psteps_to_nsteps_l c1 c3 :
    psteps c1 c3 -> ∃ n c2, step g c1 c2 ∧ nsteps n c2 c3.
  Proof using Type.
    intros (? & ? & (? & ?)%steps_to_nsteps)%psteps_inv_l. by do 2 eexists.
  Qed.

  Lemma psteps_to_nsteps_r c1 c3 :
    psteps c1 c3 -> ∃ n c2, nsteps n c1 c2 ∧ step g c2 c3.
  Proof using Type.
    intros (? & (? & ?)%steps_to_nsteps & ?)%psteps_inv_r. by do 2 eexists.
  Qed.
End Clos.

Instance steps_refl_inst {Λ: lang} {E: genv Λ} : Reflexive (steps E).
Proof using Type. intros ?. by apply steps_refl. Qed.

Instance steps_trans_inst {Λ: lang} {E: genv Λ} : Transitive (steps E).
Proof using Type. intros ? ? ?. by apply steps_trans. Qed.

Instance steps_trans_pre {Λ: lang} {E: genv Λ} : PreOrder (steps E).
Proof using Type. split; auto using steps_trans_inst, steps_refl_inst. Qed.

Instance psteps_trans_inst {Λ: lang} {E: genv Λ} : Transitive (psteps E).
Proof using Type. intros ? ? ?. by apply psteps_trans. Qed.

(* Without Event *)
Notation "E ⊨ c '->>' d" :=
  (step E c d)
    (at level 40, c at next level, d at next level, no associativity).

Notation "E ⊨ c '->>*' d" :=
  (steps E c d)
    (at level 40, c at next level, d at next level, no associativity).

Notation "E ⊨ c '->>+' d" :=
  (psteps E c d)
    (at level 40, c at next level, d at next level, no associativity).

Notation "E ⊨ c '->>_' '(' n ')' d" :=
  (nsteps E n c d)
    (at level 40, c at next level, n at level 200, d at next level, no associativity).
