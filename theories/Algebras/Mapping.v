From RSL Require Import Prelude.
From RSL Require Import Algebras.RA.
From RSL Require Import Algebras.BaseRA.

(** * Constructing a camera [B] through a mapping into [A]

The mapping may restrict the domain (i.e., we have an injection from [B] to [A],
not a bijection) and validity. These two restrictions work on opposite "ends" of
[A] according to [≼]: domain restriction must prove that when an element is in
the domain, so is its composition with other elements; validity restriction must
prove that if the composition of two elements is valid, then so are both of the
elements. The "domain" is the image of [g] in [A], or equivalently the part of
[A] where [f] returns [Some]. *)

Lemma inj_ra_mixin_restrict_validity {A : ra} {B : Type}
  `{EqDecision B} `{PCore B} `{Op B} `{Valid B}
  (f : A -> option B) (g : B -> A)
  (* [g] is injective *)
  (g_equiv : ∀ y1 y2, y1 = y2 <-> g y1 = g y2)
  (* [g] is surjective into the part of [A] where [is_Some ∘ f] holds
  (and [f] its inverse) *)
  (gf : ∀ (x : A) (y : B), f x = Some y <-> g y = x)
  (* [g] commutes with [pcore] (on the part where it is defined) and [op] *)
  (g_pcore : ∀ (y cy : B),
    pcore y = Some cy <-> pcore (g y) = Some (g cy))
  (g_op : ∀ (y1 y2 : B), g (y1 ⋅ y2) = g y1 ⋅ g y2)
  (* [g] also commutes with [opM] when the right-hand side is produced by [f],
  and cancels the [f]. In particular this axiom implies that when taking an
  element in the domain ([g y]), its composition with *any* [x : A] is still in
  the domain, and [f] computes the preimage properly.
  Note that just requiring "the composition of two elements from the domain
  is in the domain" is insufficient for this lemma to hold. [g_op] already shows
  that this is the case, but the issue is that in [pcore_mono] we obtain a
  [g y1 ≼ g y2], and the existentially quantified "remainder" in the [≼] has no
  reason to be in the domain, so [g_op] is too weak to turn this into some
  relation between [y1] and [y2] in [B]. At the same time, [g_opM_f] does not
  impl [g_op] since we need [g_op] to prove that [⋅] in [B] respects [=].
  Therefore both [g_op] and [g_opM_f] are required for this lemma to work. *)
  (g_opM_f : ∀ (x : A) (y : B), g (y ⋅? f x) = g y ⋅ x)
  (* The validity predicate on [B] restricts the one on [A] *)
  (g_valid : ∀ (y : B), ✓ y → ✓ (g y))
  (* The validity predicate on [B] satisfies the laws of validity *)
  (valid_op_l : ∀ (y1 y2 : B), ✓ (y1 ⋅ y2) → ✓ y1) :
  RaMixin B.
Proof.
  (* Some general derived facts that will be useful later. *)
  assert (fg : ∀ y, f (g y) = Some y).
  { intros. apply gf. done. }
  (* Some of the CMRA properties are useful in proving the others. *)
  assert (b_pcore_l' : ∀ y cy : B, pcore y = Some cy → cy ⋅ y = y).
  { intros y cy Hy. apply g_equiv. rewrite g_op. apply ra_pcore_l'.
    apply g_pcore. done. }
  assert (b_pcore_idemp : ∀ y cy : B, pcore y = Some cy → pcore cy = Some cy).
  { intros y cy Hy. eapply g_pcore, ra_pcore_idemp', g_pcore. done. }
  (* Now prove all the mixin laws. *)
  split.
  - intros y1 y2 y3. apply g_equiv. by rewrite !g_op, ra_assoc.
  - intros y1 y2. apply g_equiv. by rewrite !g_op, ra_comm.
  - intros y cy Hcy. apply b_pcore_l'. by rewrite Hcy.
  - intros y cy Hcy. eapply b_pcore_idemp. by rewrite <-Hcy.
  - intros y1 y2 cy [z Hy2] Hy1.
    destruct (ra_pcore_mono' (g y1) (g y2) (g cy)) as (cx&Hcgy2&[x Hcx]).
    { exists (g z). rewrite <-g_op. by apply g_equiv. }
    { apply g_pcore. by rewrite Hy1. }
    apply (reflexive_eq (R:=equiv)) in Hcgy2.
    rewrite <- g_opM_f in Hcx. rewrite Hcx in Hcgy2.
    apply g_pcore in Hcgy2.
    subst. eexists. split; first done.
    destruct (f x) as [y|].
    + exists y. done.
    + exists cy. apply (reflexive_eq (R:=equiv)), b_pcore_idemp, b_pcore_l' in Hy1.
      by rewrite Hy1.
  - done.
Qed.

(** Constructing a CMRA through an isomorphism that may restrict validity. *)
Lemma iso_ra_mixin_restrict_validity {A : ra} {B : Type}
  `{EqDecision B} `{PCore B} `{Op B} `{Valid B}
  (f : A → B) (g : B → A)
  (* [g] is proper and injective *)
  (g_equiv : ∀ y1 y2, y1 = y2 <-> g y1 = g y2)
  (* [g] is surjective (and [f] its inverse) *)
  (gf : ∀ x : A, g (f x) = x)
  (* [g] commutes with [pcore] and [op] *)
  (g_pcore : ∀ y : B, pcore (g y) = g <$> pcore y)
  (g_op : ∀ y1 y2, g (y1 ⋅ y2) = g y1 ⋅ g y2)
  (* The validity predicate on [B] restricts the one on [A] *)
  (g_valid : ∀ y, ✓ y → ✓ (g y))
  (* The validity predicate on [B] satisfies the laws of validity *)
  (valid_op_l : ∀ (y1 y2 : B), ✓ (y1 ⋅ y2) → ✓ y1) :
  RaMixin B.
Proof.
  apply (inj_ra_mixin_restrict_validity (λ x, Some (f x)) g); try done.
  - intros. split.
    + intros Hy%(inj Some). by rewrite <-Hy, gf.
    + intros ?. f_equiv. apply g_equiv. rewrite gf. done.
  - intros. rewrite g_pcore. split.
    + intros ->. done.
    + intros (?&->&?%g_equiv)%fmap_Some_1. congruence.
  - intros ??. simpl. by rewrite g_op, gf.
Qed.

(** * Constructing a ressource algebra through an isomorphism *)
Lemma iso_ra_mixin {A : ra} {B : Type}
  `{EqDecision B} `{PCore B} `{Op B} `{Valid B}
  (f : A → B) (g : B → A)
  (* [g] is proper and injective *)
  (g_equiv : ∀ y1 y2, y1 = y2 <-> g y1 = g y2)
  (* [g] is surjective (and [f] its inverse) *)
  (gf : ∀ x : A, g (f x) = x)
  (* [g] commutes with [pcore], [op], [valid] *)
  (g_pcore : ∀ y : B, pcore (g y) = g <$> pcore y)
  (g_op : ∀ y1 y2, g (y1 ⋅ y2) = g y1 ⋅ g y2)
  (g_valid : ∀ y, ✓ (g y) <-> ✓ y):
  RaMixin B.
Proof.
  apply (iso_ra_mixin_restrict_validity f g); auto.
  - by intros y ?%g_valid.
  - intros y1 y2. rewrite <-!g_valid, g_op. apply ra_valid_op_l.
Qed.
