From RSL Require Import Prelude.

From RSL Require Export Algebras.RA.
From RSL Require Export Algebras.BaseRA.

(** * Frame preserving updates *)
(* This quantifies over [option A] for the frame.  That is necessary to
   make the following hold:
     x ~~> P → Some c ~~> Some P
 *)

Definition ra_updateP {A : ra} (x : A) (P : A → Prop) := ∀ mz,
  ✓ (x ⋅? mz) -> ∃ y, P y ∧ ✓ (y ⋅? mz).
Infix "~~>:" := ra_updateP (at level 70).

Definition ra_update {A : ra} (x y : A) := ∀ mz,
  ✓ (x ⋅? mz) -> ✓ (y ⋅? mz).
Infix "~~>" := ra_update (at level 70).

Section updates.
  Context {A : ra}.
  Implicit Types x y : A.

  Lemma ra_update_updateP x y : x ~~> y ↔ x ~~>: (y =.).
  Proof using Type.
    split; intros Hup z ?; eauto.
    destruct (Hup z) as (?&<-&?); auto.
  Qed.

  Lemma ra_updateP_id (P : A → Prop) x : P x → x ~~>: P.
  Proof using Type. intros ? mz ?; eauto. Qed.

  Lemma ra_updateP_compose (P Q : A → Prop) x :
    x ~~>: P → (∀ y, P y → y ~~>: Q) → x ~~>: Q.
  Proof using Type.
    intros Hx Hy mz ?. destruct (Hx mz) as (y&?&?); naive_solver.
  Qed.

  Lemma ra_updateP_compose_l (Q : A → Prop) x y : x ~~> y → y ~~>: Q → x ~~>: Q.
  Proof using Type.
    rewrite ra_update_updateP.
    intros; apply ra_updateP_compose with (y =.); naive_solver.
  Qed.

  Lemma ra_updateP_weaken (P Q : A → Prop) x :
    x ~~>: P → (∀ y, P y → Q y) → x ~~>: Q.
  Proof using Type. eauto using ra_updateP_compose, ra_updateP_id. Qed.

  (** Updates form a preorder. *)
  (** We set this rewrite relation's cost above the stdlib's
      ([impl], [iff], [eq], ...) and [≡] but below [⊑].
      [eq] (at 100) < [≡] (at 150) < [ra_update] (at 170) < [⊑] (at 200) *)
  Global Instance ra_update_rewrite_relation :
    RewriteRelation (@ra_update A) | 170 := {}.

  Global Instance ra_update_preorder : PreOrder (@ra_update A).
  Proof using Type.
    split.
    - intros x. by apply ra_update_updateP, ra_updateP_id.
    - intros x y z. rewrite !ra_update_updateP.
      eauto using ra_updateP_compose with subst.
  Qed.

  Global Instance ra_update_proper_update :
    Proper (flip ra_update ==> ra_update ==> impl) (@ra_update A).
  Proof using Type.
    intros x1 x2 Hx y1 y2 Hy ?. etrans; [apply Hx|]. by etrans; [|apply Hy].
  Qed.

  Global Instance ra_update_flip_proper_update :
    Proper (ra_update ==> flip ra_update ==> flip impl) (@ra_update A).
  Proof using Type.
    intros x1 x2 Hx y1 y2 Hy ?. etrans; [apply Hx|]. by etrans; [|apply Hy].
  Qed.

  Lemma ra_updateP_op (P1 P2 Q : A → Prop) x1 x2 :
    x1 ~~>: P1 → x2 ~~>: P2 → (∀ y1 y2, P1 y1 → P2 y2 → Q (y1 ⋅ y2)) →
    x1 ⋅ x2 ~~>: Q.
  Proof using Type.
    intros Hx1 Hx2 Hy mz ?.
    destruct (Hx1 (Some (x2 ⋅? mz))) as (y1&?&?).
    { by simpl; rewrite <- ra_op_opM_assoc. }
    destruct (Hx2 (Some (y1 ⋅? mz))) as (y2&?&?).
    { by simpl; rewrite <-ra_op_opM_assoc, (ra_comm x2), ra_op_opM_assoc. }
    exists (y1 ⋅ y2); split; auto.
    now rewrite (ra_comm y1), ra_op_opM_assoc.
  Qed.

  Lemma ra_updateP_op' (P1 P2 : A → Prop) x1 x2 :
    x1 ~~>: P1 → x2 ~~>: P2 →
    x1 ⋅ x2 ~~>: λ y, ∃ y1 y2, y = y1 ⋅ y2 ∧ P1 y1 ∧ P2 y2.
  Proof using Type. eauto 10 using ra_updateP_op. Qed.

  Lemma ra_update_op x1 x2 y1 y2 : x1 ~~> y1 → x2 ~~> y2 → x1 ⋅ x2 ~~> y1 ⋅ y2.
  Proof using Type.
    rewrite !ra_update_updateP; eauto using ra_updateP_op with congruence.
  Qed.

  Global Instance ra_update_op_proper :
    Proper (ra_update ==> ra_update ==> ra_update) (op (A:=A)).
  Proof using Type. intros x1 x2 Hx y1 y2 Hy. by apply ra_update_op. Qed.

  Global Instance ra_update_op_flip_proper :
    Proper (flip ra_update ==> flip ra_update ==> flip ra_update) (op (A:=A)).
  Proof using Type. intros x1 x2 Hx y1 y2 Hy. by apply ra_update_op. Qed.

  Lemma ra_update_op_l x y : x ⋅ y ~~> x.
  Proof using Type.
    intros mz. rewrite ra_comm, ra_op_opM_assoc. apply ra_valid_op_r.
  Qed.

  Lemma ra_update_op_r x y : x ⋅ y ~~> y.
  Proof using Type.
    rewrite ra_comm. apply ra_update_op_l.
  Qed.

  Lemma ra_update_included x y : x ≼ y → y ~~> x.
  Proof using Type. intros [z ->]. apply ra_update_op_l. Qed.

  Lemma ra_update_valid0 x y : (✓ x → x ~~> y) → x ~~> y.
  Proof using Type.
    intros H mz Hmz. apply H, Hmz.
    destruct mz.
    - eapply ra_valid_op_l, Hmz.
    - apply Hmz.
  Qed.

  (** ** Frame preserving updates for total and discete RAs *)
  Lemma ra_total_updateP `{!RaTotal A} x (P : A → Prop) :
    x ~~>: P ↔ ∀ z, ✓ (x ⋅ z) → ∃ y, P y ∧ ✓ (y ⋅ z).
  Proof using Type.
    split; intros Hup; [intros z; apply (Hup (Some z))|].
    intros [z|] ?; simpl; [by apply Hup|].
    destruct (Hup (core x)) as (y&?&?); first by rewrite ra_core_r.
    eauto using ra_valid_op_l.
  Qed.

  Lemma ra_total_update `{!RaTotal A} x y :
    x ~~> y ↔ ∀ z, ✓ (x ⋅ z) → ✓ (y ⋅ z).
  Proof using Type.
    rewrite ra_update_updateP, ra_total_updateP. naive_solver.
  Qed.

End updates.

(** * Transport *)
Section ra_transport.
  Context  {A B : ra} (H : A = B).
  Abbreviation T := (ra_transport H).

  Lemma ra_transport_updateP (P : A → Prop) (Q : B → Prop) x :
    x ~~>: P → (∀ y, P y → Q (T y)) → T x ~~>: Q.
  Proof using Type. destruct H; eauto using ra_updateP_weaken. Qed.

  Lemma ra_transport_updateP' (P : A → Prop) x :
    x ~~>: P → T x ~~>: λ y, ∃ y', y = ra_transport H y' ∧ P y'.
  Proof using Type. eauto using ra_transport_updateP. Qed.
End ra_transport.

(** * Isomorphism *)
Section iso_ra.
  Context {A B : ra} (f : A → B) (g : B → A).

  Lemma iso_ra_updateP (P : B → Prop) (Q : A → Prop) y
      (gf : ∀ x, g (f x) = x)
      (g_op : ∀ y1 y2, g (y1 ⋅ y2) = g y1 ⋅ g y2)
      (g_valid : ∀ y, ✓ (g y) ↔ ✓ y) :
    y ~~>: P →
    (∀ y', P y' → Q (g y')) →
    g y ~~>: Q.
  Proof using Type.
    intros Hup Hx mz Hmz.
    destruct (Hup (f <$> mz)) as (y'&HPy'&Hy'%g_valid).
    { apply g_valid. destruct mz as [z|]; simpl in *; [|done].
      by rewrite g_op, gf. }
    exists (g y'); split; [by eauto|].
    destruct mz as [z|]; simpl in *; [|done].
    revert Hy'. by rewrite g_op, gf.
  Qed.

  Lemma iso_ra_updateP' (P : B → Prop) y
      (gf : ∀ x, g (f x) = x)
      (g_op : ∀ y1 y2, g (y1 ⋅ y2) = g y1 ⋅ g y2)
      (g_valid : ∀ y, ✓ (g y) ↔ ✓ y) :
    y ~~>: P ->
    g y ~~>: λ x, ∃ y, x = g y ∧ P y.
  Proof using Type. eauto using iso_ra_updateP. Qed.
End iso_ra.

Section update_lift_ra.
  Context {A B : ra}.
  Implicit Types a : A.
  Implicit Types b : B.

  (** This lemma shows that if [f] maps non-deterministic updates from [B] to [A]
  (i.e., [ra_updateP] / [~~>:]), then [f] also maps deterministic updates from
  [B] to [A] (i.e., [ra_update] / [~~>]) *)
  Lemma ra_update_lift_updateP (f : B → A) b b' :
    (∀ P, b ~~>: P → f b ~~>: λ a', ∃ b', a' = f b' ∧ P b') →
    b ~~> b' →
    f b ~~> f b'.
  Proof using Type.
    intros Hgen Hupd.
    eapply ra_update_updateP, ra_updateP_weaken.
    { eapply Hgen, ra_update_updateP, Hupd. }
    naive_solver.
  Qed.

End update_lift_ra.

(** * Product *)
Section prod.
  Context {A B : ra}.
  Implicit Types x : A * B.

  Lemma prod_updateP P1 P2 (Q : A * B → Prop) x :
    x.1 ~~>: P1 → x.2 ~~>: P2 → (∀ a b, P1 a → P2 b → Q (a,b)) → x ~~>: Q.
  Proof using Type.
    intros Hx1 Hx2 HP mz [??]; simpl in *.
    destruct (Hx1 (fst <$> mz)) as (a&?&?); first by destruct mz.
    destruct (Hx2 (snd <$> mz)) as (b&?&?); first by destruct mz.
    exists (a,b); repeat split; destruct mz; auto.
  Qed.
  Lemma prod_updateP' P1 P2 x :
    x.1 ~~>: P1 → x.2 ~~>: P2 → x ~~>: λ y, P1 (y.1) ∧ P2 (y.2).
  Proof using Type. eauto using prod_updateP. Qed.
  Lemma prod_update x y : x.1 ~~> y.1 → x.2 ~~> y.2 → x ~~> y.
  Proof using Type.
    rewrite !ra_update_updateP.
    destruct x, y; eauto using prod_updateP with subst.
  Qed.
End prod.

(** * Option *)
Section option.
  Context {A : ra}.
  Implicit Types x y : A.

  Lemma option_updateP (P : A → Prop) (Q : option A → Prop) x :
    x ~~>: P → (∀ y, P y → Q (Some y)) → Some x ~~>: Q.
  Proof using Type.
    intros Hx Hy; apply ra_total_updateP; intros [y|] ?.
    { destruct (Hx (Some y)) as (y'&?&?); auto. exists (Some y'); auto. }
    destruct (Hx None) as (y'&?&?); rewrite ?ra_core_r; auto.
    by exists (Some y'); auto.
  Qed.

  Lemma option_updateP' (P : A → Prop) x :
    x ~~>: P → Some x ~~>: from_option P False.
  Proof using Type. eauto using option_updateP. Qed.

  Lemma option_update x y : x ~~> y → Some x ~~> Some y.
  Proof using Type. rewrite !ra_update_updateP; eauto using option_updateP with subst. Qed.
End option.
