From stdpp Require Import prelude.

Lemma nsteps_inv_l {A : Type} {R : relation A} :
  ∀ n x z, nsteps R (S n) x z → ∃ y : A, R x y ∧ nsteps R n y z.
Proof. intros n x z H; inv H; eexists; eauto. Qed.

Variant psteps {A: Type} (R: relation A) : relation A :=
| pstep_intro x y z : R x y -> rtc R y z -> psteps R x z.

Lemma pstep_inv_l {A: Type} {R : relation A} :
  ∀ x z, psteps R x z <-> ∃ y : A, R x y ∧ rtc R y z.
Proof.
  intros x z. split; intros H.
  - inv H; eexists; now eauto.
  - destruct H as (y & Hstep & Hrtc). econstructor; now eauto.
Qed.

Lemma pstep_inv_r {A: Type} {R : relation A} :
  ∀ x z, psteps R x z <-> ∃ y : A, rtc R x y ∧ R y z.
Proof.
  intros x z; split; intros H.
  - inv H as [? ? ? Hs Hrtc].
    induction Hrtc as [y | x' y z Hstep Hrtc IH ] in x, y, z, Hrtc, Hs |- *.
    + exists x; split; eauto; constructor.
    + apply IH in Hstep. destruct Hstep as (y' & ? & ?).
      eexists; split; eauto; econstructor; now eauto.
  - destruct H as (y & Hrtc & Hstep).
    inv Hrtc.
    + repeat econstructor; assumption.
    + econstructor; eauto. eapply rtc_r; eassumption.
Qed.

Lemma pstep_nsteps {A: Type} {R : relation A} :
  ∀ x y, psteps R x y <-> ∃ n, nsteps R n x y ∧ n > 0.
Proof.
  intros x y; split; intros H.
  - inv H as [a b c Hstep Hrtc]. apply rtc_nsteps_1 in Hrtc.
    destruct Hrtc as [n Hnsteps]. eexists (S n); split; try lia.
    econstructor; eassumption.
  - destruct H as [[] [Hstep Hlt]]; try lia.
    inv Hstep as [ | ? ? ? ? Hr Hnsteps ]. apply rtc_nsteps_2 in Hnsteps.
    econstructor; eassumption.
Qed.

Definition EM := ∀ P, P ∨ ~P.

Section ClassicalFacts.
  Hypothesis EM : EM.

  Lemma DNE P : ~~P -> P.
  Proof. pose proof (EM P). tauto. Qed.

  Lemma not_ex_all_not {T: Type} (P: T -> Prop) :
    ~ (∃ n, P n) -> ∀ n, ~ P n.
  Proof.
    unfold not; intros notex n abs.
    apply notex.
    exists n; trivial.
  Qed.

  Lemma not_and_imply P Q :
    ~(P ∧ Q) -> P -> ~Q.
  Proof. tauto. Qed.

  Lemma not_or_and P Q : ~ (P ∨ Q) -> ~ P ∧ ~ Q.
  Proof. tauto. Qed.

End ClassicalFacts.
