From RSL Require Import Prelude.

From Stdlib.QArith Require Import Qcanon.
From Stdlib Require Import ssreflect.

From RSL.Algebras Require Import View GMap Frac DFrac.
From RSL.Algebras Require Import LocalUpdates ProofModeClasses.

(** * CMRA for a "view of a gmap".

The authoritative element [gmap_view_auth] is any [gmap K V].  The fragments
[gmap_view_frag] represent ownership of a single key in that map.  Ownership is
governed by a discardable fraction, which provides the possibiltiy to obtain
persistent read-only ownership of a key.

The key frame-preserving updates are [gmap_view_alloc] to allocate a new key,
[gmap_view_update] to update a key given full ownership of the corresponding
fragment, and [gmap_view_persist] to make a key read-only by discarding any
fraction of the corresponding fragment. Crucially, the latter does not require
owning the authoritative element.

NOTE: The API surface for [gmap_view] is experimental and subject to change.  We
plan to add notations for authoritative elements and fragments, and hope to
support arbitrary maps as fragments. *)

Local Definition gmap_view_fragURA
     (K : Type) `{Countable K} (V : ra) : ura :=
  gmapURA K (prodRA dfracRA V).

(** View relation. *)
Section rel.
  Context (K : Type) `{Countable K} (V : ra).
  Implicit Types (m : gmap K V) (k : K) (v : V).
  Implicit Types (f : gmap K (dfrac * V)).

  (* If we exactly followed [auth], we'd write something like [f ≼{n} m ∧ ✓{n} m],
  which is equivalent to:
  [map_Forall (λ k fv, ∃ v, m !! k = Some v ∧ Some fv ≼{n} Some v ∧ ✓{n} v) f].
  (Note the use of [Some] in the inclusion; the elementwise RA might not have a
  unit and we want a reflexive relation!) However, [f] and [m] do not have the
  same type, so this definition does not type-check: the fractions have been
  erased from the authoritative [m]. So we additionally quantify over the erased
  fraction [dq] and [(dq, v)] becomes the authoritative value.

  An alternative definition one might consider is to replace the erased fraction
  by a hard-coded [DfracOwn 1], the biggest possible fraction. That would not
  work: we would end up with [Some dv ≼{n} Some (DfracOwn 1, v)] but that cannot
  be satisfied if [dv.1 = DfracDiscarded], a case that we definitely want to
  allow!

  It is possible that [∀ k, ∃ dq, let auth := (pair dq) <$> m !! k in ✓{n} auth
  ∧ f !! k ≼{n} auth] would also work, but now the proofs are all done already.  ;)
  The two are probably equivalent, with a proof similar to [lookup_includedN]? *)
  Local Definition gmap_view_rel_raw m f :=
    map_Forall (λ k fv,
      ∃ v dq, m !! k = Some v ∧ ✓ (dq, v) ∧ (Some fv ≼ Some (dq, v))) f.

  Local Lemma gmap_view_rel_raw_mono m f1 f2 :
    gmap_view_rel_raw m f1 →
    f2 ≼ f1 →
    gmap_view_rel_raw m f2.
  Proof using Type.
    unfold gmap_view_rel_raw.
    intros Hrel Hm k [dqa va] Hk.
    destruct (lookup_included f2 f1) as [Hf _].
    unfold map_Forall in Hrel.
    pose proof (Hf Hm k) as Hk2.
    rewrite Hk in Hk2.
    destruct (Some_included_is_Some _ _ _ Hk2) as [[q' va'] Heq].
    specialize (Hrel _ _ Heq) as (v & dq & Hm1 & [Hvval Hdqval] & Hvincl). simpl in *.
    eexists. exists dq. split; first done. split.
    { now split. }
    etransitivity; eauto.
    by rewrite Heq.
  Qed.

  Local Lemma gmap_view_rel_raw_valid m f :
    gmap_view_rel_raw m f → ✓ f.
  Proof using Type.
    intros Hrel k. destruct (f !! k) as [[dqa va]|] eqn:Hf; rewrite Hf; last done.
    specialize (Hrel _ _ Hf) as (v & dq & Hmval & Hvval & Hvincl). simpl in *.
    eapply ra_valid_included. 2:done. done.
  Qed.

  Local Lemma gmap_view_rel_raw_unit :
    ∃ m, gmap_view_rel_raw m ε.
  Proof using Type. exists ∅. apply: map_Forall_empty. Qed.

  Local Canonical Structure gmap_view_rel :
      view_rel (gmap K V) (gmap_view_fragURA K V) :=
    ViewRel _ _ gmap_view_rel_raw gmap_view_rel_raw_mono
            gmap_view_rel_raw_valid gmap_view_rel_raw_unit.

  Local Lemma gmap_view_rel_exists f :
    (∃ m, gmap_view_rel m f) ↔ ✓ f.
  Proof using Type.
    split.
    { intros [m Hrel]. eapply gmap_view_rel_raw_valid, Hrel. }
    intros Hf.
    cut (∃ m, gmap_view_rel m f ∧ ∀ k, f !! k = None → m !! k = None).
    { naive_solver. }
    induction f as [|k [dq v] f Hk' IH] using map_ind.
    { exists ∅. split; [|done]. apply: map_Forall_empty. }
    move: (Hf k). rewrite lookup_insert_eq=> -[/= ??].
    destruct IH as (m & Hm & Hdom).
    { intros k'. destruct (decide (k = k')) as [->|?]; [by rewrite Hk'|].
      move: (Hf k'). by rewrite lookup_insert_ne. }
    exists (<[k:=v]> m).
    rewrite /gmap_view_rel /= /gmap_view_rel_raw map_Forall_insert //=. split_and!.
    - exists v, dq. split; first by rewrite lookup_insert_eq.
      split; first by split. done.
    - eapply map_Forall_impl; [apply Hm|]; simpl.
      intros k' [dq' ag'] (v'&?&?&?). exists v'.
      rewrite lookup_insert_ne; naive_solver.
    - intros k'. rewrite !lookup_insert_None. naive_solver.
  Qed.

  Local Lemma gmap_view_rel_unit m : gmap_view_rel m ε.
  Proof using Type. apply: map_Forall_empty. Qed.
End rel.

(** [gmap_view] is a notation to give canonical structure search the chance
to infer the right instances (see [auth]). *)
Abbreviation gmap_view K V := (view (gmap_view_rel_raw K V)).

Definition gmap_viewRA (K : Type) `{Countable K} (V : ra) : ra :=
  viewRA _ _ (gmap_view_rel K V).

Definition gmap_viewURA (K : Type) `{Countable K} (V : ra) : ura :=
  viewURA _ _ (gmap_view_rel K V).

Section definitions.
  Context `{Countable K} {V : ra}.

  Definition gmap_view_auth (dq : dfrac) (m : gmap K V) : gmap_viewRA K V :=
    ●V{dq} m.
  Definition gmap_view_frag (k : K) (dq : dfrac) (v : V) : gmap_viewRA K V :=
    ◯V {[k := (dq, v)]}.
End definitions.

Section lemmas.
  Context `{Countable K} {V : ra}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (dq : dfrac) (v : V).

  (* Helper lemmas *)
  Local Lemma gmap_view_rel_lookup m k dq v :
    gmap_view_rel K V m {[k := (dq, v)]} ↔
    ∃ v' dq', m !! k = Some v' ∧ ✓ (dq', v') ∧ Some (dq, v) ≼ Some (dq', v').
  Proof using Type.
    split.
    - intros Hrel.
      edestruct (Hrel k) as (v' & dq' & Hlookup & Hval & Hinc).
      { rewrite lookup_singleton_eq. done. }
      simpl in *. eexists _, _. split_and!; done.
    - intros (v' & dq' & Hlookup & Hval & ?) j [df va].
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton_eq. intros [= <- <-]. simpl.
      exists v', dq'. split_and!; by rewrite ?Hv'.
  Qed.

  (** Composition and validity *)
  Lemma gmap_view_auth_dfrac_op dp dq m :
    gmap_view_auth (dp ⋅ dq) m =
    gmap_view_auth dp m ⋅ gmap_view_auth dq m.
  Proof using Type. by rewrite /gmap_view_auth view_auth_dfrac_op. Qed.
  Global Instance gmap_view_auth_dfrac_is_op dq dq1 dq2 m :
    IsOp dq dq1 dq2 →
    IsOp' (gmap_view_auth dq m) (gmap_view_auth dq1 m) (gmap_view_auth dq2 m).
  Proof using Type. rewrite /gmap_view_auth. apply _. Qed.

  Lemma gmap_view_auth_dfrac_op_inv dp m1 dq m2 :
    ✓ (gmap_view_auth dp m1 ⋅ gmap_view_auth dq m2) → m1 = m2.
  Proof using Type. apply view_auth_dfrac_op_inv. Qed.

  Lemma gmap_view_auth_dfrac_valid m dq : ✓ gmap_view_auth dq m ↔ ✓ dq.
  Proof using Type.
    rewrite view_auth_dfrac_valid. intuition eauto using gmap_view_rel_unit.
  Qed.
  Lemma gmap_view_auth_valid m : ✓ gmap_view_auth (DfracOwn 1) m.
  Proof using Type. rewrite gmap_view_auth_dfrac_valid. done. Qed.

  Lemma gmap_view_auth_dfrac_op_valid dq1 dq2 m1 m2 :
    ✓ (gmap_view_auth dq1 m1 ⋅ gmap_view_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 = m2.
  Proof using Type.
    rewrite view_auth_dfrac_op_valid. intuition eauto using gmap_view_rel_unit.
  Qed.

  Lemma gmap_view_auth_op_valid m1 m2 :
    ✓ (gmap_view_auth (DfracOwn 1) m1 ⋅ gmap_view_auth (DfracOwn 1) m2) ↔ False.
  Proof using Type. apply view_auth_op_valid. Qed.

  Lemma gmap_view_frag_valid k dq v : ✓ gmap_view_frag k dq v ↔ ✓ dq ∧ ✓ v.
  Proof using Type.
    rewrite view_frag_valid gmap_view_rel_exists singleton_validN pair_valid.
    naive_solver.
  Qed.

  Lemma gmap_view_frag_op k dq1 dq2 v1 v2 :
    gmap_view_frag k (dq1 ⋅ dq2) (v1 ⋅ v2) =
      gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2.
  Proof using Type. rewrite -view_frag_op singleton_op -pair_op //. Qed.

  Lemma gmap_view_frag_add k q1 q2 v1 v2 :
    gmap_view_frag k (DfracOwn (q1 + q2)) (v1 ⋅ v2) =
      gmap_view_frag k (DfracOwn q1) v1 ⋅ gmap_view_frag k (DfracOwn q2) v2.
  Proof using Type. rewrite -gmap_view_frag_op. done. Qed.

  Lemma gmap_view_frag_op_valid k dq1 dq2 v1 v2 :
    ✓ (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ↔
      ✓ (dq1 ⋅ dq2) ∧ ✓ (v1 ⋅ v2).
  Proof using Type.
    rewrite view_frag_valid gmap_view_rel_exists singleton_op singleton_validN.
    by rewrite -pair_op pair_valid.
  Qed.

  Lemma gmap_view_both_dfrac_valid dp m k dq v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) ↔
      ∃ v' dq', ✓ dp ∧ m !! k = Some v' ∧ ✓ (dq', v') ∧
                Some (dq, v) ≼ Some (dq', v').
  Proof using Type.
    rewrite /gmap_view_auth /gmap_view_frag.
    rewrite view_both_dfrac_valid gmap_view_rel_lookup. naive_solver.
  Qed.

  Lemma gmap_view_both_valid dp m k v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k (DfracOwn 1) v) ↔
      ✓ dp ∧ ✓ v ∧ m !! k = Some v.
  Proof using Type.
    rewrite gmap_view_both_dfrac_valid. split.
    - intros (v' & dq' & Hdq & Hlookup & Hvalid & Hincl).
      split; first done. rewrite Hlookup.
      pose proof (Some_included_exclusive _ _ _  Hincl Hvalid) as Heq.
      inv Heq. split.
      + rewrite pair_valid in Hvalid. naive_solver.
      + auto.
    - intros (Hdp & Hval & Hlookup).
      exists v, (DfracOwn 1). do 2 (split; [done|]). split.
      + rewrite pair_valid. split; auto. easy.
      + by apply: Some_included_refl.
  Qed.
  (** The backwards direction here does not hold: if [dq = DfracOwn 1] but
  [v ≠ v'], we have to find a suitable erased fraction [dq'] to satisfy the view
  relation, but there is no way to satisfy [Some (DfracOwn 1, v) ≼{n} Some (dq', v')]
  for any [dq']. The "if and only if" version of this lemma would have to
  involve some extra condition like [dq = DfracOwn 1 → v = v'], or phrased
  more like the view relation itself: [∃ dq', ✓ dq' ∧ Some (v, dq) ≼{n} Some (v', dq')]. *)
  Lemma gmap_view_both_dfrac_valid_total `{!RaTotal V} dp m k dq v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) →
    ∃ v', ✓ dp ∧ ✓ dq ∧ m !! k = Some v' ∧ ✓ v' ∧ v ≼ v'.
  Proof using Type.
    rewrite gmap_view_both_dfrac_valid.
    intros (v' & dq' & Hdp & Hlookup & Hvalid & Hincl).
    exists v'. split; first done. split.
    - eapply (ra_valid_Some_included _ dq'); first by apply Hvalid.
      eapply Some_pair_included_l. done.
    - split; first done. split; first apply Hvalid.
      move:Hincl=> /Some_pair_included_r /Some_included_total. done.
  Qed.

  (** Without [RaDiscrete], we cannot do much better than [∀ n, <same as above>].
  This is because both the [dq'] and the witness for the [≼{n}] can be different for
  each step-index. It is totally possible that at low step-indices, [v] has a frame
  (and [dq' > dq]) while at higher step-indices, [v] has no frame (and [dq' = dq]). *)
  Lemma gmap_view_both_dfrac_valid_discrete dp m k dq v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) ↔
      ∃ v' dq', ✓ dp ∧ m !! k = Some v' ∧
                ✓ (dq', v') ∧
                Some (dq, v) ≼ Some (dq', v').
  Proof using Type.
    rewrite gmap_view_both_dfrac_valid. split.
    - intros Hvalid.
      destruct Hvalid as (v' & dq' & Hdp & Hlookup & Hvalid & Hincl).
      exists v', dq'. do 2 (split; first done).
      split; easy.
    - intros (v' & dq' & Hdp & Hlookup & Hvalid & Hincl).
      exists v', dq'. do 2 (split; first done).
      split; easy.
  Qed.
  (** The backwards direction here does not hold: if [dq = DfracOwn 1] but
  [v ≠ v'], we have to find a suitable erased fraction [dq'] to satisfy the view
  relation, but there is no way to satisfy [Some (DfracOwn 1, v) ≼ Some (dq', v')]
  for any [dq']. The "if and only if" version of this lemma would have to
  involve some extra condition like [dq = DfracOwn 1 → v = v'], or phrased
  more like the view relation itself: [∃ dq', ✓ dq' ∧ Some (v, dq) ≼ Some (v', dq')]. *)
  Lemma gmap_view_both_dfrac_valid_discrete_total `{!RaTotal V} dp m k dq v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) →
    ∃ v', ✓ dp ∧ ✓ dq ∧ m !! k = Some v' ∧ ✓ v' ∧ v ≼ v'.
  Proof using Type.
    rewrite gmap_view_both_dfrac_valid_discrete.
    intros (v' & dq' & Hdp & Hlookup & Hvalid & Hincl).
    exists v'. split; first done. split.
    - eapply (ra_valid_Some_included _ dq'); first by apply Hvalid.
      eapply Some_pair_included_l. done.
    - split; first done. split; first apply Hvalid.
      move:Hincl=> /Some_pair_included_r /Some_included_total. done.
  Qed.

  (** Frame-preserving updates *)
  Lemma gmap_view_alloc m k dq v :
    m !! k = None →
    ✓ dq →
    ✓ v →
    gmap_view_auth (DfracOwn 1) m ~~>
      gmap_view_auth (DfracOwn 1) (<[k := v]> m) ⋅ gmap_view_frag k dq v.
  Proof using Type.
    intros Hfresh Hdq Hval. apply view_update_alloc=> bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { destruct (bf !! k) as [[df' va']|] eqn:Hbf; last done.
        specialize (Hrel _ _ Hbf). destruct Hrel as (v' & dq' & Hm & _).
        exfalso. rewrite Hm in Hfresh. done. }
      rewrite lookup_singleton_eq Hbf right_id.
      intros [= <- <-]. eexists _, _.
      rewrite lookup_insert_eq. split; first done.
      split; last by apply: Some_included_refl.
      split; done.
    - simpl. rewrite lookup_singleton_ne; auto.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & ? & Hm & ?).
      eexists _, _. split; last done.
      rewrite lookup_insert_ne //.
  Qed.

  (* Lemma gmap_view_alloc_big m m' dq : *)
  (*   m' ##ₘ m → *)
  (*   ✓ dq → *)
  (*   map_Forall (λ k v, ✓ v) m' → *)
  (*   gmap_view_auth (DfracOwn 1) m ~~> *)
  (*     gmap_view_auth (DfracOwn 1) (m' ∪ m) ⋅ *)
  (*     ([^op map] k↦v ∈ m', gmap_view_frag k dq v). *)
  (* Proof using Type. *)
  (*   intros ?? Hm'. *)
  (*   induction m' as [|k v m' ? IH] using map_ind; decompose_map_disjoint. *)
  (*   { rewrite big_opM_empty left_id_L right_id. done. } *)
  (*   apply map_Forall_insert in Hm' as [??]; last done. *)
  (*   rewrite IH //. rewrite big_opM_insert // assoc. *)
  (*   apply ra_update_op; last done. *)
  (*   rewrite -insert_union_l. apply (gmap_view_alloc _ k dq); [|done..]. *)
  (*   by apply lookup_union_None. *)
  (* Qed. *)

  Lemma gmap_view_delete m k v :
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k (DfracOwn 1) v ~~>
    gmap_view_auth (DfracOwn 1) (delete k m).
  Proof using Type.
    apply view_update_dealloc=>bf Hrel j [df va] Hbf /=.
    destruct (decide (j = k)) as [->|Hne].
    - edestruct (Hrel k) as (v' & dq' & ? & Hval & Hincl).
      { rewrite lookup_op Hbf lookup_singleton_eq -Some_op. done. }
      eapply (ra_valid_Some_included _ _ _ Hval) in Hincl as Hval'.
      exfalso. clear Hval Hincl.
      rewrite pair_valid /= in Hval'.
      apply: dfrac_full_exclusive. apply Hval'.
    - edestruct (Hrel j) as (v' & ? & ? & ?).
      { rewrite lookup_op lookup_singleton_ne // Hbf. done. }
      eexists v', _. split; last done.
      rewrite lookup_delete_ne //.
  Qed.

  (* Lemma gmap_view_delete_big m m' : *)
  (*   gmap_view_auth (DfracOwn 1) m ⋅ *)
  (*   ([^op map] k↦v ∈ m', gmap_view_frag k (DfracOwn 1) v) ~~> *)
  (*     gmap_view_auth (DfracOwn 1) (m ∖ m'). *)
  (* Proof using Type. *)
  (*   induction m' as [|k v m' ? IH] using map_ind. *)
  (*   { rewrite right_id_L big_opM_empty right_id //. } *)
  (*   rewrite big_opM_insert //. *)
  (*   rewrite [gmap_view_frag _ _ _ ⋅ _]comm assoc IH gmap_view_delete. *)
  (*   rewrite -delete_difference. done. *)
  (* Qed. *)

  (** We do not use [local_update] ([~l~>]) in the premise because we also want
  to expose the role of the fractions. *)
  Lemma gmap_view_update m k dq v mv' v' dq' :
    (∀ mv f,
      m !! k = Some mv →
      ✓ ((dq, v) ⋅? f) →
      mv = v ⋅? (snd <$> f) →
      ✓ ((dq', v') ⋅? f) ∧ mv' = v' ⋅? (snd <$> f)) →
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k dq v ~~>
      gmap_view_auth (DfracOwn 1) (<[k := mv']> m) ⋅ gmap_view_frag k dq' v'.
  Proof using Type.
    intros Hup. apply view_update=> bf Hrel j [df va].
    rewrite lookup_op.
    destruct (decide (j = k)) as [->|Hne]; last first.
    { (* prove that other keys are unaffected *)
      simplify_map_eq.
      rewrite left_id. intros Hbf.
      edestruct (Hrel j) as (mva & mdf & Hlookup & Hval & Hincl).
      { rewrite lookup_op lookup_singleton_ne // left_id //. }
      naive_solver. }
    simplify_map_eq. intros Hbf.
    edestruct (Hrel k) as (mv & mdf & Hlookup & Hval & Hincl).
    { rewrite lookup_op lookup_singleton_eq // Some_op_opM //. }
    rewrite Some_included_opM in Hincl.
    destruct Hincl as [f' Hincl]. rewrite ra_opM_opM_assoc in Hincl.
    set f := bf !! k ⋅ f'. (* the complete frame *)
    change (bf !! k ⋅ f') with f in Hincl.
    specialize (Hup mv f). destruct Hup as (Hval' & Hincl').
    { done. }
    { rewrite -Hincl. done. }
    { by destruct f as [[]|]; simpl in *; inv Hincl. }
    eexists mv', (dq' ⋅? (fst <$> f)). split; first done.
    rewrite -Hbf. clear Hbf. split.
    - rewrite Hincl'. destruct Hval'. by destruct f.
    - rewrite Some_op_opM. rewrite Some_included_opM.
      exists f'. rewrite Hincl'.
      rewrite ra_opM_opM_assoc. change (bf !! k ⋅ f') with f.
      by destruct f.
  Qed.

  (** This derived version cannot exploit [dq = DfracOwn 1]. *)
  Lemma gmap_view_update_local m k dq mv v mv' v' :
    m !! k = Some mv →
    (mv, v) ~l~> (mv', v') →
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k dq v ~~>
    gmap_view_auth (DfracOwn 1) (<[k := mv']> m) ⋅ gmap_view_frag k dq v'.
  Proof using Type.
    intros Hlookup Hup. apply gmap_view_update.
    intros mv0 f Hmv0 Hval Hincl.
    rewrite Hlookup in Hmv0. injection Hmv0 as [= <-].
    specialize (Hup (snd <$> f)). destruct Hup as (Hval' & Hincl').
    { rewrite Hincl. destruct Hval. by destruct f. }
    { simpl. done. }
    split; last done. split.
    - destruct Hval. by destruct f.
    - simpl in *. replace (((dq, v') ⋅? f).2) with (v' ⋅? (snd <$> f)).
      2:{ by destruct f. }
      rewrite -Hincl'. done.
  Qed.

  Lemma gmap_view_replace m k v v' :
    ✓ v' →
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k (DfracOwn 1) v ~~>
      gmap_view_auth (DfracOwn 1) (<[k := v']> m) ⋅ gmap_view_frag k (DfracOwn 1) v'.
  Proof using Type.
    (* There would be a simple proof via delete-then-insert... but we use this as a
       sanity check to make sure the update lemma is strong enough. *)
    intros Hval'. apply gmap_view_update.
    intros mv f Hlookup Hval Hincl.
    destruct f; simpl.
    { apply exclusive_l in Hval; first done. apply _. }
    split; last done.
    split; first done. simpl. done.
  Qed.

  (* Lemma gmap_view_replace_big m m0 m1 : *)
  (*   dom m0 = dom m1 → *)
  (*   map_Forall (λ k v, ✓ v) m1 → *)
  (*   gmap_view_auth (DfracOwn 1) m ⋅ *)
  (*   ([^op map] k↦v ∈ m0, gmap_view_frag k (DfracOwn 1) v) ~~> *)
  (*     gmap_view_auth (DfracOwn 1) (m1 ∪ m) ⋅ *)
  (*     ([^op map] k↦v ∈ m1, gmap_view_frag k (DfracOwn 1) v). *)
  (* Proof using Type. *)
  (*   intros Hdom%eq_sym. revert m1 Hdom. *)
  (*   induction m0 as [|k v m0 Hnotdom IH] using map_ind; intros m1 Hdom Hval. *)
  (*   { rewrite dom_empty_L in Hdom. *)
  (*     apply dom_empty_iff_L in Hdom as ->. *)
  (*     rewrite left_id_L big_opM_empty. done. } *)
  (*   rewrite dom_insert_L in Hdom. *)
  (*   assert (k ∈ dom m1) as Hindom by set_solver. *)
  (*   apply elem_of_dom in Hindom as [v' Hlookup]. *)
  (*   rewrite big_opM_insert //. *)
  (*   rewrite [gmap_view_frag _ _ _ ⋅ _]comm assoc. *)
  (*   rewrite (IH (delete k m1)); last first. *)
  (*   { by apply map_Forall_delete. } *)
  (*   { rewrite dom_delete_L Hdom. *)
  (*     apply not_elem_of_dom in Hnotdom. set_solver -Hdom. } *)
  (*   rewrite -assoc [_ ⋅ gmap_view_frag _ _ _]comm assoc. *)
  (*   rewrite (gmap_view_replace _ _ _ v'). *)
  (*   2:{ eapply Hval. done. } *)
  (*   rewrite (big_opM_delete _ m1 k v') // -assoc. *)
  (*   rewrite insert_union_r; last by rewrite lookup_delete_eq. *)
  (*   rewrite union_delete_insert //. *)
  (* Qed. *)

  Lemma gmap_view_auth_persist dq m :
    gmap_view_auth dq m ~~> gmap_view_auth DfracDiscarded m.
  Proof using Type. apply view_update_auth_persist. Qed.

  Lemma gmap_view_auth_unpersist m :
    gmap_view_auth DfracDiscarded m ~~>: λ a, ∃ q, a = gmap_view_auth (DfracOwn q) m.
  Proof using Type. apply view_updateP_auth_unpersist. Qed.

  Local Lemma gmap_view_frag_dfrac k dq P v :
    dq ~~>: P →
    gmap_view_frag k dq v ~~>: λ a, ∃ dq', a = gmap_view_frag k dq' v ∧ P dq'.
  Proof using Type.
    intros Hdq.
    eapply ra_updateP_weaken;
      [apply view_updateP_frag
         with (P := λ b', ∃ dq', ◯V b' = gmap_view_frag k dq' v ∧ P dq')
      |naive_solver].
    intros m bf Hrel.
    destruct (Hrel k ((dq, v) ⋅? bf !! k)) as (v' & dq' & Hlookup & Hval & Hincl).
    { by rewrite lookup_op lookup_singleton_eq Some_op_opM. }
    rewrite Some_included_opM in Hincl.
    destruct Hincl as [f' Hincl]. rewrite ra_opM_opM_assoc in Hincl.
    set f := bf !! k ⋅ f'. (* the complete frame *)
    change (bf !! k ⋅ f') with f in Hincl.
    destruct (Hdq (option_map fst f)) as (dq'' & HPdq'' & Hvdq'').
    { destruct f as [[]|]; inv Hincl; simpl in *; apply Hval. }
    eexists. split; first by exists dq''.
    intros j [df va] Heq.
    destruct (decide (k = j)) as [->|Hne].
    - rewrite lookup_op lookup_singleton_eq in Heq.
      eexists v', (dq'' ⋅? (fst <$> f)).
      split; first done. split.
      + split; last by apply Hval. simpl. done.
      + rewrite -Heq. exists f'.
        rewrite -ra_assoc. change (bf !! j ⋅ f') with f.
        destruct f as [[]|]; inv Hincl; easy.
    - rewrite lookup_op lookup_singleton_ne // left_id in Heq.
      eapply Hrel. rewrite lookup_op lookup_singleton_ne // left_id Heq //.
  Qed.

  Lemma gmap_view_frag_persist k dq v :
    gmap_view_frag k dq v ~~> gmap_view_frag k DfracDiscarded v.
  Proof using Type.
    eapply (ra_update_lift_updateP (λ dq, gmap_view_frag k dq v)).
    - intros. by apply gmap_view_frag_dfrac.
    - apply dfrac_discard_update.
  Qed.

  Lemma gmap_view_frag_unpersist k v :
    gmap_view_frag k DfracDiscarded v ~~>:
      λ a, ∃ q, a = gmap_view_frag k (DfracOwn q) v.
  Proof using Type.
    eapply ra_updateP_weaken.
    { apply gmap_view_frag_dfrac, dfrac_undiscard_update. }
    naive_solver.
  Qed.

  (** Typeclass instances *)
  Global Instance gmap_view_frag_core_id k dq v :
    CoreId dq → CoreId v → CoreId (gmap_view_frag k dq v).
  Proof using Type.
    intros Hdq Hv. apply view_frag_core_id.
    unfold CoreId. unfold pcore. simpl.
    unfold gmap_pcore_instance. f_equal.
    rewrite omap_singleton.
    unfold pcore. simpl.
    unfold prod_pcore_instance. simpl.
    by rewrite Hdq Hv.
  Qed.

  Global Instance gmap_view_frag_mut_is_op dq dq1 dq2 k v v1 v2 :
    IsOp dq dq1 dq2 →
    IsOp v v1 v2 →
    IsOp' (gmap_view_frag k dq v) (gmap_view_frag k dq1 v1) (gmap_view_frag k dq2 v2).
  Proof using Type. rewrite /IsOp' /IsOp => -> ->. apply gmap_view_frag_op. Qed.
End lemmas.

Global Typeclasses Opaque gmap_view_auth gmap_view_frag.
