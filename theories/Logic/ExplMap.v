From RSL Require Import Prelude.

From RSL.Logic Require Export iFreeSim.

From iris.algebra Require Export gmap.
From iris.algebra.lib Require Export excl_auth.

From iris.base_logic.lib Require Export own.

Class expl_mapG Σ A B `{Countable A, Countable B} :=
  ExplG
    {
      #[local] expl_map_inG :: inG Σ (excl_authR (gmap A (leibnizO B)));
    }.

Global Hint Mode expl_mapG - ! ! - - - - : typeclass_instances.

Definition expl_mapΣ A B `{Countable A, Countable B}: gFunctors :=
  #[ GFunctor (excl_authR (gmapO A (leibnizO B))) ].

Global Instance subG_expl_mapΣ `{Countable A, Countable B} Σ :
  subG (expl_mapΣ A B) Σ → expl_mapG Σ A B.
Proof using Type. solve_inG. Qed.


Definition eauth_map `{expl_mapG Σ A B} m : excl_authR (gmap A _) :=
  (excl_auth_auth (A:=gmap A (leibnizO B)) m).

Definition efrag_map `{expl_mapG Σ A B} m : excl_authR (gmap A _) :=
  (excl_auth_frag (A:=gmap A (leibnizO B)) m).

Definition expl_map_auth_def `{expl_mapG Σ A B} (γ : gname) (m : gmap A B) : iProp Σ :=
  own γ (eauth_map m).

Definition expl_map_auth_aux : seal (@expl_map_auth_def).
Proof using Type. by eexists. Qed.
Definition expl_map_auth := unseal expl_map_auth_aux.
Local Lemma expl_map_auth_eq : @expl_map_auth = @expl_map_auth_def.
Proof using Type. by apply seal_eq. Qed.

Global Arguments expl_map_auth {_ _ _ _ _ _ _ _}.


Definition expl_map_frag_def `{expl_mapG Σ A B} (γ : gname) (m : gmap A B) : iProp Σ :=
  own γ (efrag_map m).

Definition expl_map_frag_aux : seal (@expl_map_frag_def).
Proof using Type. by eexists. Qed.
Definition expl_map_frag := unseal expl_map_frag_aux.
Local Lemma expl_map_frag_eq : @expl_map_frag = @expl_map_frag_def.
Proof using Type. by apply seal_eq. Qed.

Global Arguments expl_map_frag {_ _ _ _ _ _ _ _}.

Section inv.
  Context `{expl_mapG Σ A B}.
  Implicit Types (m : gmap A B) (L : gset (B * A)).

  Definition expl_map_wf m L : Prop :=
    ∀ ls, is_Some (m !! ls) -> ∃ lt, (lt, ls) ∈ L.

  Lemma expl_map_wf_init L:
    expl_map_wf ∅ L.
  Proof using Type. by intros ls [? Hm]. Qed.

  Lemma expl_map_wf_extend_L m L L':
    expl_map_wf m L →
    expl_map_wf m (L' ∪ L).
  Proof using Type.
    intros Hwf ls Hm. destruct (Hwf _ Hm) as [lt Hin]. exists lt. by set_solver.
  Qed.

  Definition expl_map_inv γ m L : iProp Σ :=
    expl_map_auth γ m ∗ ⌜expl_map_wf m L⌝.

  Lemma expl_map_alloc m L :
    expl_map_wf m L ->
    ⊢ |==> ∃ γ, expl_map_inv γ m L ∗ expl_map_frag γ m.
  Proof using Type.
    intros Hwf.
    unfold expl_map_inv.
    rewrite expl_map_frag_eq expl_map_auth_eq.
    iMod (own_alloc (eauth_map m ⋅ efrag_map m)) as (γ) "[Hauth Hfrag]".
    { apply excl_auth_valid. }
    iExists γ.
    iFrame. by iPureIntro.
  Qed.

  Lemma expl_map_wf_insert γ m L m' ls lt :
    (lt, ls) ∈ L ->
    expl_map_inv γ m L -∗
    expl_map_frag γ m' ==∗
    expl_map_inv γ (<[ls := lt]> m) L ∗ expl_map_frag γ (<[ls := lt]> m).
  Proof using Type.
    remember (<[ls:=lt]>m) as m''.
    iIntros (Hin) "[Hauth %Hwf] Hfrag".
    unfold expl_map_inv.
    rewrite expl_map_auth_eq expl_map_frag_eq.
    iMod (own_update_2 γ _ _ (eauth_map m'' ⋅ efrag_map m'') with "Hauth Hfrag")
      as "[Hauth Hfrag]".
    { apply excl_auth_update. }
    iModIntro. iFrame. iPureIntro.
    subst m''. intros ls' Hm.
    destruct (decide (ls = ls')) as [-> | Hneq].
    - by exists lt.
    - rewrite lookup_insert_ne in Hm; by auto.
  Qed.

  Lemma expl_map_wf_delete γ m m' L ls :
    expl_map_inv γ m L -∗
    expl_map_frag γ m' ==∗
    expl_map_inv γ (delete ls m) L ∗expl_map_frag γ (delete ls m).
  Proof using Type.
    remember (delete ls m) as m''.
    iIntros "[Hauth %Hwf] Hfrag".
    unfold expl_map_inv.
    rewrite expl_map_auth_eq expl_map_frag_eq.
    iMod (own_update_2 γ _ _ (eauth_map m'' ⋅ efrag_map m'') with "Hauth Hfrag")
      as "[Hauth Hfrag]".
    { apply excl_auth_update. }
    iModIntro. iFrame. iPureIntro.
    subst m''. intros ls' [Hne Hm]%lookup_delete_is_Some.
    by auto.
  Qed.

  Lemma expl_map_inv_agree γ m m' L :
    expl_map_inv γ m L -∗
    expl_map_frag γ m' -∗
    ⌜m = m'⌝.
  Proof using Type.
    iIntros "[Hauth _] Hfrag".
    rewrite expl_map_auth_eq expl_map_frag_eq.
    iPoseProof (own_valid_2 with "Hauth Hfrag") as "%Hv".
    iPureIntro. by apply excl_auth_agree_L in Hv.
  Qed.
End inv.
