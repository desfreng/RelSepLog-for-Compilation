From iris.algebra Require Export view gset.
From iris.algebra Require Import updates.

From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.

Section gset_view_rel.
  Context {SI : sidx} `{Countable A}.
  Implicit Types (S aSet fSet: gset A).

  Local Definition gset_view_rel_raw (n : SI) aSet fSet: Prop := fSet ⊆ aSet.

  Local Lemma gset_view_rel_raw_mono n1 n2 aSet1 aSet2 fSet1 fSet2:
    gset_view_rel_raw n1 aSet1 fSet1 →
    aSet1 ≡{n2}≡ aSet2 →
    fSet2 ≼{n2} fSet1 →
    (n2 ≤ n1)%sidx →
    gset_view_rel_raw n2 aSet2 fSet2.
  Proof using Type.
    unfold gset_view_rel_raw.
    intros ? <-%(discrete_iff _ _ _)%leibniz_equiv ?%gset_included _.
    by transitivity fSet1.
  Qed.

  Local Lemma gset_view_rel_raw_valid n aSet fSet :
    gset_view_rel_raw n aSet fSet → ✓{n}fSet.
  Proof using Type. by intros _. Qed.

  Local Lemma gset_view_rel_raw_unit n :
    ∃ aSet, gset_view_rel_raw n aSet ε.
  Proof using Type. by exists ∅. Qed.

  Canonical Structure gset_view_rel : view_rel (gsetO A) (gsetUR A) :=
    ViewRel gset_view_rel_raw gset_view_rel_raw_mono
            gset_view_rel_raw_valid gset_view_rel_raw_unit.

  Global Instance gset_view_rel_discrete : ViewRelDiscrete gset_view_rel.
  Proof using Type. easy. Qed.

  Local Lemma gset_view_rel_iff n aSet fSet :
    gset_view_rel n aSet fSet ↔ fSet ⊆ aSet.
  Proof using Type. done. Qed.
End gset_view_rel.

Definition gset_view {SI : sidx} A `{Countable A} :=
  view (gset_view_rel_raw (A:=A)).
Definition gset_viewO {SI : sidx} A `{Countable A} : ofe :=
  viewO (gset_view_rel (A:=A)).
Definition gset_viewR {SI : sidx} A `{Countable A} : cmra :=
  viewR (gset_view_rel (A:=A)).
Definition gset_viewUR {SI : sidx} A `{Countable A} : ucmra :=
  viewUR (gset_view_rel (A:=A)).

Definition gset_view_auth {SI : sidx} `{Countable A}
  (dq : dfrac) (L : gset A) : gset_view A := ●V{dq} L ⋅ ◯V L.
Definition gset_view_elem {SI : sidx} `{Countable A}
  (a : A) : gset_view A := ◯V {[ a ]}.

(* The uCMRA we need. *)
Class gset_viewG Σ A `{Countable A} :=
  GsetViewG {
      #[local] gset_viewG_inG :: inG Σ (gset_viewR A);
    }.

Global Hint Mode gset_viewG - ! - - : typeclass_instances.

Definition gset_viewΣ A `{Countable A}: gFunctors :=
  #[ GFunctor (gset_viewR A) ].

Global Instance subG_gset_viewΣ `{Countable A} Σ :
  subG (gset_viewΣ A) Σ → gset_viewG Σ A.
Proof using Type. solve_inG. Qed.

Definition gset_view_own_auth_def `{gset_viewG Σ A}
  (γ : gname) (dq : dfrac) (L : gset A) : iProp Σ :=
  own γ (gset_view_auth dq L).

Definition gset_view_own_auth_aux : seal (@gset_view_own_auth_def).
Proof using Type. by eexists. Qed.
Definition gset_view_own_auth := unseal gset_view_own_auth_aux.
Definition gset_view_own_auth_eq : @gset_view_own_auth = @gset_view_own_auth_def.
Proof using Type. by apply seal_eq. Qed.
Global Arguments gset_view_own_auth {_ _ _ _ _}.

Definition gset_view_own_elem_def `{gset_viewG Σ A} (γ : gname) (a : A) : iProp Σ :=
  own γ (gset_view_elem a).

Definition gset_view_own_elem_aux : seal (@gset_view_own_elem_def).
Proof using Type. by eexists. Qed.
Definition gset_view_own_elem := unseal gset_view_own_elem_aux.
Definition gset_view_own_elem_eq : @gset_view_own_elem = @gset_view_own_elem_def.
Proof using Type. by apply seal_eq. Qed.
Global Arguments gset_view_own_elem {_ _ _ _ _}.

Notation "γ ↪●S dq L" :=
  (gset_view_own_auth γ dq L)
    (at level 20, dq custom dfrac at level 1, format "γ  ↪●S dq  L").

Notation "γ ↪◯S a" :=
  (gset_view_own_elem γ a) (at level 20, format "γ  ↪◯S a").

Section gset_view.
  Context `{gset_viewG Σ A}.
  Implicit Types (L : gset A) (a : A).

  Global Instance gset_view_own_auth_timeless γ dq L :
    Timeless (γ ↪●S {dq} L).
  Proof using Type. rewrite gset_view_own_auth_eq. apply _. Qed.
  Global Instance gset_view_own_auth_persistent γ L :
    Persistent (γ ↪●S□ L).
  Proof using Type. rewrite gset_view_own_auth_eq. apply _. Qed.

  Global Instance gset_view_own_elem_timeless γ a :
    Timeless (γ ↪◯S a).
  Proof using Type. rewrite gset_view_own_elem_eq. apply _. Qed.
  Global Instance gset_view_own_elem_persistent γ a :
    Persistent (γ ↪◯S a).
  Proof using Type. rewrite gset_view_own_elem_eq. apply _. Qed.

  Global Instance gset_view_own_auth_fractional γ L :
    Fractional (λ q, γ ↪●S{#q} L).
  Proof using Type.
    intros p q. rewrite gset_view_own_auth_eq -own_op.
    rewrite /gset_view_auth /gset_view_own_auth_def /gset_view_auth.
    rewrite (comm _ (●V{#q} _)) -!assoc (assoc _ (◯V _)).
    rewrite -core_id_dup (comm _ (◯V _)).
    rewrite assoc -view_auth_dfrac_op //.
  Qed.
  Global Instance gset_view_own_auth_as_fractional γ q L :
    AsFractional (γ ↪●S{#q} L) (λ q, γ ↪●S{#q} L) q.
  Proof using Type. split; [auto|apply _]. Qed.

  Lemma gset_view_own_auth_agree γ dq1 dq2 L1 L2 :
    γ ↪●S{dq1} L1 -∗ γ ↪●S{dq2} L2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ L1 = L2⌝.
  Proof using Type.
    rewrite gset_view_own_auth_eq. iIntros "H1 H2".
    iCombine "H1 H2" gives "%Hv".
    iPureIntro.
    rewrite /gset_view_own_auth_def /gset_view_auth in Hv.
    rewrite (comm _ (●V{dq2} _)) -!assoc (assoc _ (◯V _)) in Hv.
    rewrite -view_frag_op (comm _ (◯V _)) assoc in Hv.
    apply cmra_valid_op_l in Hv. rewrite view_auth_dfrac_op_valid in Hv.
    destruct Hv as (? & ? & _). split; auto.
    by apply leibniz_equiv.
  Qed.
  Lemma gset_view_own_auth_exclusive γ L1 L2 :
    γ ↪●S L1 -∗ γ ↪●S L2 -∗ False.
  Proof using Type.
    iIntros "H1 H2".
    by iDestruct (gset_view_own_auth_agree with "H1 H2") as %[[] _].
  Qed.

  Lemma gset_view_own_valid γ dq L :
    γ ↪●S{dq} L -∗ ⌜✓ dq⌝.
  Proof using Type.
    rewrite gset_view_own_auth_eq. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as "%Hv".
    iPureIntro.
    rewrite view_both_dfrac_valid in Hv.
    by destruct Hv as [? _].
  Qed.

  Lemma gset_view_own_elem_get {γ dq L} a :
    a ∈ L →
    γ ↪●S{dq} L -∗ γ ↪◯S a.
  Proof using Type.
    intros. rewrite gset_view_own_auth_eq gset_view_own_elem_eq.
    iApply own_mono. unfold gset_view_elem, gset_view_auth.
    transitivity (◯V L : gset_view A).
    - apply view_frag_mono, gset_included. set_solver.
    - unfold gset_view_auth.
      eexists. by rewrite comm.
  Qed.

  Lemma gset_view_elem_of {γ dq L} a :
    γ ↪●S{dq} L -∗ γ ↪◯S a -∗ ⌜a ∈ L⌝.
  Proof using Type.
    iIntros "Hauth Helem". rewrite gset_view_own_auth_eq gset_view_own_elem_eq.
    iCombine "Hauth Helem" gives "%Ha".
    iPureIntro.
    unfold gset_view_auth, gset_view_elem in Ha.
    rewrite -assoc -view_frag_op view_both_dfrac_valid in Ha.
    destruct Ha as [_ Hin].
    setoid_rewrite gset_view_rel_iff in Hin. pose 0ᵢ. set_solver.
  Qed.

  Lemma gset_view_own_elem_get_big γ dq L :
    γ ↪●S{dq} L -∗ [∗ set] a ∈ L, γ ↪◯S a.
  Proof using Type.
    iIntros "Hauth". iApply big_sepS_forall. iIntros (a ?) "/=".
    by iApply gset_view_own_elem_get.
  Qed.

  Lemma gset_view_own_alloc L :
    ⊢ |==> ∃ γ, γ ↪●S L ∗ [∗ set] a ∈ L, γ ↪◯S a.
  Proof using Type.
    iAssert (∃ γ, γ ↪●S L)%I with "[>]" as (γ) "Hauth".
    { rewrite gset_view_own_auth_eq. iApply own_alloc.
      apply view_both_dfrac_valid. split.
      - easy.
      - intros. by rewrite gset_view_rel_iff.
    }
    iExists γ. iModIntro. iSplit; [done|].
    by iApply gset_view_own_elem_get_big.
  Qed.
  Lemma gset_view_own_alloc_empty :
    ⊢ |==> ∃ γ, γ ↪●S (∅ : gset A).
  Proof using Type. iMod (gset_view_own_alloc ∅) as (γ) "[Hauth _]"; by auto. Qed.

  Lemma gset_view_own_extend {γ L} a :
    a ∉ L ->
    γ ↪●S L ==∗
    γ ↪●S ({[ a ]} ∪ L) ∗ γ ↪◯S a.
  Proof using Type.
    iIntros (?) "Hauth".
    iAssert (γ ↪●S ({[a]} ∪ L)) with "[> Hauth]" as "Hauth".
    { rewrite gset_view_own_auth_eq. iApply (own_update with "Hauth").
      apply view_update. intros n aSet.
      rewrite !gset_view_rel_iff !gset_op.
      by set_solver. }
    iModIntro. iSplit; [done|].
    iApply (gset_view_own_elem_get with "Hauth"). set_solver.
  Qed.

  Lemma gset_view_own_extend_internal {γ L} a :
    (γ ↪◯S a -∗ False) -∗
    γ ↪●S L ==∗
    γ ↪●S ({[ a ]} ∪ L) ∗ γ ↪◯S a.
  Proof using Type.
    iIntros "Ha HL".
    iAssert ⌜a ∉ L⌝%I as %?.
    { iIntros (?). iApply ("Ha"). by iApply gset_view_own_elem_get. }
    by iApply (gset_view_own_extend with "HL").
  Qed.
End gset_view.
