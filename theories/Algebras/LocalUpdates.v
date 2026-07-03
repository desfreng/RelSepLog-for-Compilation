From RSL Require Import Prelude.

From RSL Require Export Algebras.RA.
From RSL Require Export Algebras.BaseRA.

(** * Local updates *)
Definition local_update {A : ra} (x y : A * A) :=
  ∀ mz,
    ✓ fst x ->
    fst x = snd x ⋅? mz ->
    ✓ fst y ∧ fst y = snd y ⋅? mz.
Global Instance: Params (@local_update) 2 := {}.
Infix "~l~>" := local_update (at level 70).

Section updates.
  Context {A : ra}.
  Implicit Types x y : A.

  Global Instance local_update_preorder : PreOrder (@local_update A).
  Proof using Type. split; unfold local_update; red; naive_solver. Qed.

  Lemma exclusive_local_update `{!Exclusive y} x x' : ✓ x' → (x,y) ~l~> (x',x').
  Proof using Type.
    intros ? mz Hxv Hx; simpl in *.
    revert Hxv; rewrite Hx.
    intros ->%exclusive_opM; auto.
  Qed.

  Lemma op_local_update x y z :
    (✓ x → ✓ (z ⋅ x)) → (x, y) ~l~> (z ⋅ x, z ⋅ y).
  Proof using Type.
    intros Hv mz Hxv Hx; simpl in *; split; [by auto|].
    by rewrite Hx, <-ra_op_opM_assoc.
  Qed.

  Lemma op_local_update_frame x y x' y' yf :
    (x,y) ~l~> (x',y') → (x,y ⋅ yf) ~l~> (x', y' ⋅ yf).
  Proof using Type.
    intros Hup mz Hxv Hx; simpl in *.
    destruct (Hup (Some (yf ⋅? mz))); [done|simpl; by rewrite <-ra_op_opM_assoc|].
    by rewrite ra_op_opM_assoc.
  Qed.

  Lemma cancel_local_update x y z `{!Cancelable x} :
    (x ⋅ y, x ⋅ z) ~l~> (y, z).
  Proof using Type.
    intros f ? Heq. split; first by eapply ra_valid_op_r.
    apply (cancelable x); first done. by rewrite <-ra_op_opM_assoc.
  Qed.

  Lemma replace_local_update x y `{!IdFree x} :
    ✓ y → (x, x) ~l~> (y, y).
  Proof using Type.
    intros ? mz ? Heq; simpl in *; split; auto.
    destruct mz as [z|]; [|done].
    by destruct (id_free_r x z).
  Qed.

  Lemma core_id_local_update x y z `{!CoreId y} :
    y ≼ x → (x, z) ~l~> (x, z ⋅ y).
  Proof using Type.
    intros Hincl mf ? Heq; simpl in *; split; first done.
    apply core_id_extract in Hincl; auto.
    rewrite Hincl, Heq. destruct mf as [f|]; last done.
    simpl. by rewrite <-ra_assoc, (ra_comm f y), ra_assoc.
  Qed.

  Lemma local_update_valid x y x' y' :
    (✓ x → ✓ y → Some y ≼ Some x → (x,y) ~l~> (x',y')) →
    (x,y) ~l~> (x',y').
  Proof using Type.
    intros Hup mz Hmz Hz; simpl in *. apply Hup; auto.
    - revert Hmz; rewrite Hz. destruct mz; simpl; eauto using ra_valid_op_l.
    - apply Some_included_opM. eauto.
  Qed.

  Lemma local_update_total_valid `{!RaTotal A} x y x' y' :
    (✓ x → ✓ y → y ≼ x → (x,y) ~l~> (x',y')) → (x,y) ~l~> (x',y').
  Proof using Type.
    intros Hup. apply local_update_valid. intros ?? Hincl. apply Hup; auto.
    by apply Some_included_total.
  Qed.
End updates.

Section updates_unital.
  Context {A : ura}.
  Implicit Types x y : A.

  Lemma local_update_unital x y x' y' :
    (x,y) ~l~> (x',y') ↔ ∀ z,
      ✓ x → x = y ⋅ z → ✓ x' ∧ x' = y' ⋅ z.
  Proof using Type.
    split.
    - intros Hup z. apply (Hup (Some z)).
    - intros Hup [z|]; simpl; [by auto|].
      intros Hx ->. apply Hup with (z:= ε) in Hx.
      + destruct Hx as [? ->]; split; auto.
        apply ura_unit_r.
      + symmetry. apply ura_unit_r.
  Qed.

  Lemma cancel_local_update_unit x y `{!Cancelable x} :
    (x ⋅ y, x) ~l~> (y, ε).
  Proof using Type.
    rewrite <-(@ura_unit_r _ x) at 2.
    by apply cancel_local_update.
  Qed.
End updates_unital.

Section updates_unit.
  (** * Unit *)
  Lemma unit_local_update (x y x' y' : unit) : (x, y) ~l~> (x', y').
  Proof using Type. destruct x,y,x',y'; reflexivity. Qed.
End updates_unit.


Section updates_product.
  (** * Product *)
  Lemma prod_local_update {A B : ra} (x y x' y' : A * B) :
    (x.1, y.1) ~l~> (x'.1, y'.1) → (x.2, y.2) ~l~> (x'.2, y'.2) →
    (x, y) ~l~> (x', y').
  Proof using Type.
    intros Hup1 Hup2 mz [Hx1 Hx2] Hx; simpl in *.
    destruct (Hup1 (fst <$> mz)); [done|by subst;destruct mz|].
    destruct (Hup2 (snd <$> mz)); [done|by subst;destruct mz|].
    destruct x', y'. simpl in *; subst.
    by destruct mz.
  Qed.

  Lemma prod_local_update' {A B : ra} (x1 y1 x1' y1' : A) (x2 y2 x2' y2' : B) :
    (x1,y1) ~l~> (x1',y1') → (x2,y2) ~l~> (x2',y2') →
    ((x1,x2),(y1,y2)) ~l~> ((x1',x2'),(y1',y2')).
  Proof using Type. intros. by apply prod_local_update. Qed.

  Lemma prod_local_update_1 {A B : ra} (x1 y1 x1' y1' : A) (x2 y2 : B) :
    (x1,y1) ~l~> (x1',y1') → ((x1,x2),(y1,y2)) ~l~> ((x1',x2),(y1',y2)).
  Proof using Type. intros. by apply prod_local_update. Qed.

  Lemma prod_local_update_2 {A B : ra} (x1 y1 : A) (x2 y2 x2' y2' : B) :
    (x2,y2) ~l~> (x2',y2') → ((x1,x2),(y1,y2)) ~l~> ((x1,x2'),(y1,y2')).
  Proof using Type. intros. by apply prod_local_update. Qed.
End updates_product.

Section updates_option.
  (** * Option *)
  Lemma option_local_update {A : ra} (x y x' y' : A) :
    (x, y) ~l~> (x',y') →
    (Some x, Some y) ~l~> (Some x', Some y').
  Proof using Type.
    intros Hup. apply local_update_unital. intros mz Hxv Hx; simpl in *.
    destruct (Hup mz); first done.
    { destruct mz as [?|]; inversion_clear Hx; auto. }
    split; first done.
    simpl in *. subst. destruct mz as [?|]; auto.
  Qed.

  Lemma option_local_update_None {A: ura} (x x' y': A):
    (x, ε) ~l~> (x', y') ->
    (Some x, None) ~l~> (Some x', Some y').
  Proof using Type.
    intros Hup. apply local_update_unital. intros mz.
    intros Hv He. subst.
    destruct (Hup (Some x)); simpl in *; first done.
    - symmetry. apply ura_unit_l.
    - split; first done. subst. rewrite Some_op.
      destruct mz; inv He; auto.
  Qed.

  Lemma alloc_option_local_update {A : ra} (x : A) y :
    ✓ x →
    (None, y) ~l~> (Some x, Some x).
  Proof using Type.
    intros Hx. apply local_update_unital. intros z ? Heq.
    destruct y, z; inv Heq. now split.
  Qed.

  Lemma delete_option_local_update {A : ra} (x : option A) (y : A) :
    Exclusive y → (x, Some y) ~l~> (None, None).
  Proof using Type.
    intros Hex. apply local_update_unital. intros z Hy Heq.
    split; first done.
    destruct z as [z|]; last done. exfalso.
    revert Hy. rewrite Heq. simpl. rewrite <-Some_op. intros Hy. eapply Hex.
    eapply Hy.
  Qed.

  Lemma delete_option_local_update_cancelable {A : ra} (mx : option A) :
    Cancelable mx → (mx, mx) ~l~> (None, None).
  Proof using Type.
    intros ?. apply local_update_unital. intros mf. simpl. intros Hmx Heq.
    split; first done.
    rewrite @ura_unit_l. eapply (cancelable mx); auto; by destruct mx.
  Qed.
End updates_option.
