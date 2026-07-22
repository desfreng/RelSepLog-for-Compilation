From RSL Require Import Prelude.

From stdpp Require Import gmap.

Section bij_set.
  Context `{Countable A, Countable B}.
  Implicit Types (a : A) (b : B) (p: A * B) (L: gset (A * B)).

  Definition bij_set L :=
    ∀ a b,
    (a, b) ∈ L ->
    (∀ b', (a, b') ∈ L -> b' = b) ∧
    (∀ a', (a', b) ∈ L -> a' = a).

  Lemma bij_set_empty : bij_set ∅.
  Proof using Type. by intros ?? []%not_elem_of_empty. Qed.

  Lemma bij_set_extend L a b :
    bij_set L ->
    (∀ b', (a, b') ∉ L) ->
    (∀ a', (a', b) ∉ L) ->
    bij_set ({[(a, b)]} ∪ L).
  Proof using Type.
    intros Hbij Ha Hb a' b' [He%elem_of_singleton|Hin]%elem_of_union.
    - inv He. split.
      + intros ? [He%elem_of_singleton|Hin]%elem_of_union.
        * by inv He.
        * exfalso. by eapply Ha.
      + intros ? [He%elem_of_singleton|Hin]%elem_of_union.
        * by inv He.
        * exfalso. by eapply Hb.
    - split.
      + intros ? [He%elem_of_singleton|Hin']%elem_of_union.
        * exfalso. by inv He; eapply Ha.
        * by eapply Hbij.
      + intros ? [He%elem_of_singleton|Hin']%elem_of_union.
        * exfalso. by inv He; eapply Hb.
        * by eapply Hbij.
  Qed.

  Lemma bij_set_eq_iff L a1 a2 b1 b2 :
    bij_set L ->
    (a1, b1) ∈ L ->
    (a2, b2) ∈ L ->
    a1 = a2 <-> b1 = b2.
  Proof using Type.
    intros HL H1 H2.
    destruct (HL _ _ H1) as [Hb1 Ha1].
    split; intros ->.
    - by rewrite (Hb1 _ H2).
    - by rewrite (Ha1 _ H2).
  Qed.

  Lemma bij_set_subseteq L L' :
    bij_set L -> L' ⊆ L -> bij_set L'.
  Proof using Type.
    intros Hbij Hle a b Hin.
    split.
    - intros ? Hin'. eapply Hbij; by eapply Hle.
    - intros ? Hin'. eapply Hbij; by eapply Hle.
  Qed.

  Lemma bij_set_functional L a b1 b2 :
    bij_set L ->
    (a, b1) ∈ L ->
    (a, b2) ∈ L ->
    b1 = b2.
  Proof using Type.
    intros Hbij H1 H2. by erewrite <-bij_set_eq_iff.
  Qed.

  Lemma bij_set_injective L a1 a2 b :
    bij_set L ->
    (a1, b) ∈ L ->
    (a2, b) ∈ L ->
    a1 = a2.
  Proof using Type.
    intros Hbij H1 H2. by erewrite ->bij_set_eq_iff.
  Qed.

  Lemma bij_set_intersection  L1 L2 :
    bij_set L1 -> bij_set (L1 ∩ L2).
  Proof using Type.
    intros Hbij1 a b [H1 _]%elem_of_intersection. split.
    - intros b' [H2 _]%elem_of_intersection.
      by eapply bij_set_functional.
    - intros a' [H2 _]%elem_of_intersection.
      by eapply bij_set_injective.
  Qed.

  Lemma bij_set_diff L1 L2 :
    bij_set L1 -> bij_set (L1 ∖ L2).
  Proof using Type.
    intros Hbij a b [H1 _]%elem_of_difference. split.
    - intros b' [H2 _]%elem_of_difference.
      by eapply bij_set_functional.
    - intros a' [H2 _]%elem_of_difference.
      by eapply bij_set_injective.
  Qed.

  Lemma bij_set_diff_fst_neq L a1 a2 b1 b2 :
    bij_set L ->
    (a1, b1) ∈ L ->
    (a2, b2) ∈ L ∖ {[ (a1, b1) ]} ->
    a1 ≠ a2.
  Proof using Type.
    intros Hbij H1 [H2 Hneq%not_elem_of_singleton]%elem_of_difference.
    intros ->. apply Hneq.
    f_equal. by eapply bij_set_functional.
  Qed.

  Lemma bij_set_diff_snd_neq L a1 a2 b1 b2 :
    bij_set L ->
    (a1, b1) ∈ L ->
    (a2, b2) ∈ L ∖ {[ (a1, b1) ]} ->
    b1 ≠ b2.
  Proof using Type.
    intros Hbij H1 [H2 Hneq%not_elem_of_singleton]%elem_of_difference.
    intros ->. apply Hneq.
    f_equal. by eapply bij_set_injective.
  Qed.

  Definition dom L : gset A := set_map fst L.
  Definition codom L : gset B := set_map snd L.

  Lemma dom_spec L a : a ∈ dom L <-> ∃ b, (a, b) ∈ L.
  Proof using Type.
    split.
    - intros ([] & -> & Hin)%elem_of_map. by eexists.
    - intros [b Hin]. apply elem_of_map. exists (a, b). by split.
  Qed.

  Lemma codom_spec L b : b ∈ codom L <-> ∃ a, (a, b) ∈ L.
  Proof using Type.
    split.
    - intros ([] & -> & Hin)%elem_of_map. by eexists.
    - intros [a Hin]. apply elem_of_map. exists (a, b). by split.
  Qed.

  Lemma dom_union L L' a : a ∈ dom L ∨ a ∈ dom L' <-> a ∈ dom (L ∪ L').
  Proof using Type.
    split.
    - intros [[b Hdom]%dom_spec | [b Hdom]%dom_spec];
        apply dom_spec; eexists.
      + by apply elem_of_union_l.
      + by apply elem_of_union_r.
    - intros [b [Hdom | Hdom]%elem_of_union]%dom_spec.
      + left. by apply dom_spec; eexists.
      + right. by apply dom_spec; eexists.
  Qed.

  Lemma codom_union L L' b : b ∈ codom L ∨ b ∈ codom L' <-> b ∈ codom (L ∪ L').
  Proof using Type.
    split.
    - intros [[a Hdom]%codom_spec | [a Hdom]%codom_spec];
        apply codom_spec; eexists.
      + by apply elem_of_union_l.
      + by apply elem_of_union_r.
    - intros [a [Hdom | Hdom]%elem_of_union]%codom_spec.
      + left. by apply codom_spec; eexists.
      + right. by apply codom_spec; eexists.
  Qed.

  Lemma dom_singleton a b x : x ∈ dom {[ (a, b) ]} <-> x = a.
  Proof using Type.
    split.
    - intros [y Heq%elem_of_singleton]%dom_spec. by inv Heq.
    - intros ->. apply dom_spec. eexists. by apply elem_of_singleton.
  Qed.

  Lemma codom_singleton a b y : y ∈ codom {[ (a, b) ]} <-> y = b.
  Proof using Type.
    split.
    - intros [x Heq%elem_of_singleton]%codom_spec. by inv Heq.
    - intros ->. apply codom_spec. eexists. by apply elem_of_singleton.
  Qed.
End bij_set.
