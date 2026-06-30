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
  - inv H as [x' y z' Hs Hrtc].
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

Lemma pstep_to_rtc {A: Type} {R : relation A} :
  ∀ x y, psteps R x y -> rtc R x y.
Proof.
  intros x z H. inv H as [? y ? Hstep Hrtc].
  now apply rtc_l with y.
Qed.

Lemma pstep_l {A: Type} {R : relation A} :
  ∀ x y z, R x y -> psteps R y z -> psteps R x z.
Proof.
  intros x y z HR H. inv H as [? ? ? Hstep Hrtc].
  econstructor.
  + eassumption.
  + eapply rtc_l; eassumption.
Qed.

Lemma pstep_r {A: Type} {R : relation A} :
  ∀ x y z, psteps R x y -> R y z -> psteps R x z.
Proof.
  intros x y z H HR. inv H as [? ? ? Hstep Hrtc].
  econstructor.
  + eassumption.
  + eapply rtc_r; eassumption.
Qed.

Lemma pstep_to_nstep_l {A: Type} {R : relation A} :
  ∀ x z, psteps R x z -> ∃ n y, R x y ∧ nsteps R n y z.
Proof.
  intros x z H. inv H as [? y ? Hstep Hrtc].
  destruct (rtc_nsteps_1 _ _ Hrtc) as [n Hnsteps].
  exists n. exists y. now split.
Qed.

Lemma pstep_to_nstep_r {A: Type} {R : relation A} :
  ∀ x z, psteps R x z -> ∃ n y, nsteps R n x y ∧ R y z.
Proof.
  intros x z H. apply pstep_inv_r in H.
  destruct H as (y & Hrtc & Hstep).
  destruct (rtc_nsteps_1 _ _ Hrtc) as [n Hnsteps].
  exists n. exists y. now split.
Qed.

Lemma inj_some {T: Type} : ∀ x y : T,
  Some x = Some y <-> x = y.
Proof.
  intros x y. split.
  - now injection 1.
  - now intros ->.
Qed.

Definition curry5 {A B C D E F: Type} (f : A * B * C * D * E -> F) :=
  fun x1 x2 x3 x4 x5 => f (x1, x2, x3, x4, x5).

Definition uncurry5 {A B C D E F: Type} (f : A -> B -> C -> D -> E -> F) :=
  fun '(x1, x2, x3, x4, x5) => f x1 x2 x3 x4 x5.

Definition curry6 {A B C D E F G: Type} (f : A * B * C * D * E * F -> G) :=
  fun x1 x2 x3 x4 x5 x6 => f (x1, x2, x3, x4, x5, x6).

Definition uncurry6 {A B C D E F G: Type} (f : A -> B -> C -> D -> E -> F -> G) :=
  fun '(x1, x2, x3, x4, x5, x6) => f x1 x2 x3 x4 x5 x6.
