From RSL Require Import Prelude RLogic.

From Coinduction Require Import all.

Inductive dual (X: Type) :=
  Dual : X -> dual X.

Arguments Dual {_} _.

Definition undual {X: Type} (d: dual X) : X :=
  match d with Dual x => x end.

Lemma dual_undual_id {X: Type} (x: dual X): Dual (undual x) = x.
Proof. now destruct x. Qed.

Lemma undual_dual_id {X: Type} (x: X): undual (Dual x) = x.
Proof. easy. Qed.

Global Program Instance CompleteLattice_Dual `{L: CompleteLattice X}:
  CompleteLattice (dual X) :=
  {|
    weq '(Dual a) '(Dual b) := weq a b;
    leq '(Dual a) '(Dual b) := leq b a;
    sup' I P f := Dual (inf' P (fun a => undual (f a)));
    inf' I P f := Dual (sup' P (fun a => undual (f a)));
    cup '(Dual P) '(Dual Q) := Dual (cap P Q);
    cap '(Dual P) '(Dual Q) := Dual (cup P Q);
    bot := Dual top;
    top := Dual bot
  |}.
Next Obligation.
  split.
  { split.
    - intros [a]. reflexivity.
    - intros [a] [b] [c]. etransitivity; eassumption.
  }
  split. { intros [a] [b]. now rewrite weq_spec. }
  split.
  {
    intros I P f [a]. split.
    - intros H i HP.
      rewrite inf_spec in H.
      specialize (H i).
      destruct (f i).
      now apply H.
    - intros H.
      rewrite inf_spec.
      intros i HP.
      specialize (H i HP).
      destruct (f i).
      apply H.
  }
  split.
  {
    intros I P f [a]. split.
    - intros H i HP.
      rewrite sup_spec in H.
      specialize (H i).
      destruct (f i).
      now apply H.
    - intros H.
      rewrite sup_spec.
      intros i HP.
      specialize (H i HP).
      destruct (f i).
      apply H.
  }
  split. { intros [a] [b] [c]. apply cap_spec. }
  split. { intros [a] [b] [c]. apply cup_spec. }
  split. { intros [a]. apply leq_xt. }
  { intros [a]. apply leq_bx. }
Qed.

Section lfp_def.
  Context `{L: CompleteLattice X}.

  Variable f: mon X.

  Local Lemma dual_reverse :
    ∀ x y : X, y <= x <-> Dual x <= Dual y.
  Proof using Type. intros x y. now split. Qed.

  Local Program Definition dual_f : mon (dual X) :=
    {| body := fun d => Dual (f (undual d)) |}.
  Next Obligation.
    intros [a] [b]. now apply (Hbody f).
  Qed.

  Local Lemma dual_f_spec (x: dual X) :
    Dual (f (undual x)) = dual_f x.
  Proof using Type. easy. Qed.

  Definition lfp : X :=
    undual (gfp dual_f).

  Lemma lfp_post :
    lfp <= f lfp.
  Proof using Type.
    unfold lfp.
    apply dual_reverse.
    rewrite dual_f_spec.
    rewrite dual_undual_id.
    apply leq_gfp.
    apply Hbody.
    now apply gfp_pfp.
  Qed.

  Lemma lfp_pre :
    f lfp <= lfp.
  Proof using Type.
    unfold lfp.
    apply dual_reverse.
    rewrite dual_f_spec.
    rewrite dual_undual_id.
    now apply gfp_pfp.
  Qed.

  Lemma geq_lfp x :
    f x <= x -> lfp <= x.
  Proof using Type.
    intros Hx.
    unfold lfp.
    rewrite <- undual_dual_id.
    apply dual_reverse.
    rewrite !dual_undual_id.
    now apply leq_gfp.
  Qed.

  Lemma lfp_fp :
    lfp == f lfp.
  Proof using Type.
    apply antisym.
    - apply lfp_post.
    - apply lfp_pre.
  Qed.

End lfp_def.


Global Instance lfp_leq {X L}: Proper (leq ==> leq) (@lfp X L).
Proof. intros f g fg. apply geq_lfp. rewrite fg. apply lfp_pre. Qed.

Global Instance gfp_weq {X L}: Proper (weq ==> weq) (@lfp X L) := op_leq_weq_1.
