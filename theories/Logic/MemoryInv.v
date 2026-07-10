From RSL Require Import Prelude.

From RSL.Logic Require Import GSetView.
From RSL.Commons Require Import Language.

From iris.base_logic.lib Require Import own ghost_map.
From iris.proofmode Require Import proofmode.

Class memGpreS Σ :=
  MemGpreS {
      #[local] mem_pre_heapG :: ghost_mapG Σ loc val;
      #[local] mem_pre_freedG :: gset_viewG Σ loc;
    }.

Class memGS Σ :=
  MemGS {
      #[local] mem_inG :: memGpreS Σ;

      gen_heap_name : gname;
      gen_freed_name : gname
    }.

Arguments MemGS Σ {_} _ _.
Arguments gen_heap_name {Σ} _.
Arguments gen_freed_name {Σ} _.

Definition memΣ : gFunctors :=
  #[ ghost_mapΣ loc val; gset_viewΣ loc ].

Global Instance subG_MemΣ {Σ} : subG memΣ Σ → memGpreS Σ.
Proof. solve_inG. Qed.

Section memory_defs.
  Context `{HinG : memGS Σ}.

  Local Definition memory_inv_def (m: memory): iProp Σ :=
    ∃ freed,
      ghost_map_auth (gen_heap_name HinG) 1%Qp m ∗
      gset_view_own_auth (gen_freed_name HinG) (DfracOwn 1) freed ∗
      ⌜∀ l, l ∈ freed -> m !! l = None⌝.

  Local Definition memory_inv_aux : seal (@memory_inv_def).
  Proof using Type. by eexists. Qed.
  Definition memory_inv := unseal memory_inv_aux.
  Local Lemma memory_inv_eq : @memory_inv = @memory_inv_def.
  Proof using Type. by apply seal_eq. Qed.

  Local Definition pointsto_def (l : loc) (dq : dfrac) (v : val) : iProp Σ :=
    ghost_map_elem (gen_heap_name HinG) l dq v.

  Local Definition pointsto_aux : seal (@pointsto_def).
  Proof using Type. by eexists. Qed.
  Definition pointsto := unseal pointsto_aux.
  Local Lemma pointsto_eq : @pointsto = @pointsto_def.
  Proof using Type. by apply seal_eq. Qed.

  Definition freed_def (l : loc) : iProp Σ :=
    gset_view_own_elem (gen_freed_name HinG) l.

  Local Definition freed_aux : seal (@freed_def).
  Proof using Type. by eexists. Qed.
  Definition freed := unseal freed_aux.
  Local Lemma freed_eq : @freed = @freed_def.
  Proof using Type. by apply seal_eq. Qed.
End memory_defs.

Local Ltac unseal :=
  rewrite
    ?memory_inv_eq /memory_inv_def
    ?pointsto_eq /pointsto_def
    ?freed_eq /freed_def.

Section memory_laws.
  Context `{!memGS Σ}.

  Local Notation "l ↦ v" :=
    (pointsto l (DfracOwn 1) v)
      (at level 20) : bi_scope.

  Local Notation "'free' l" :=
    (freed l)
      (at level 20) : bi_scope.

  Lemma mapsto_valid l v: l ↦ v -∗ ⌜✓ DfracOwn 1⌝.
  Proof using Type. unseal. by iApply ghost_map_elem_valid. Qed.

  Lemma mapsto_valid_2 l v1 v2: l ↦ v1 -∗ l ↦ v2 -∗ False.
  Proof using Type.
    unseal. iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as "[%H _]".
    exfalso. by apply dfrac_valid_own in H.
  Qed.

  Lemma pointsto_interp m l v:
    memory_inv m -∗
    l ↦ v -∗
    ⌜m !! l = Some v⌝.
  Proof using Type.
    unseal. iIntros "(%f & Hm & Hf & %Hinv) Hl".
    by iApply (ghost_map_lookup with "Hm Hl").
  Qed.

  Lemma free_interp m l:
    memory_inv m -∗
    free l -∗
    ⌜m !! l = None⌝.
  Proof using Type.
    unseal. iIntros "(%f & Hm & Hf & %Hinv) Hl".
    iDestruct (gset_view_elem_of with "Hf Hl") as "%".
    iPureIntro. by apply Hinv.
  Qed.

  (** Update lemmas *)
  Lemma memory_alloc m v:
    memory_inv m ==∗
    ∃ l, ⌜m !! l = None⌝ ∗
         memory_inv (<[l := v]>m) ∗ l ↦ v.
  Proof using Type.
    unseal.
    iIntros "(%f & Hm & Hf & %Hinv)".
    set (l := fresh (dom m ∪ f)).
    assert (m !! l = None).
    { apply not_elem_of_dom. intro Hf.
      eapply elem_of_union_l in Hf. apply (is_fresh _ Hf).
    }
    iMod (ghost_map_insert l v with "Hm") as "[Hm Hl]"; first done.
    iFrame. iPureIntro. split; auto.
    intros l' Hin. rewrite lookup_insert_ne; auto.
    intros <-. subst l.
    eapply elem_of_union_r in Hin.
    apply (is_fresh _ Hin).
  Qed.

  Lemma memory_update m l vold v:
    memory_inv m -∗
    l ↦ vold ==∗
    memory_inv (<[l := v]>m) ∗ l ↦ v.
  Proof using Type.
    unseal.
    iIntros "(%f & Hm & Hf & %Hinv) Hl".
    iDestruct (ghost_map_lookup with "Hm Hl") as "%Hv".
    iMod (ghost_map_update with "Hm Hl") as "[Hm Hl]".
    iModIntro. iFrame.
    iPureIntro. intros l' Hin.
    rewrite lookup_insert_ne; auto.
    intros ->. apply Hinv in Hin.
    by rewrite Hv in Hin.
  Qed.

  Lemma memory_free m l v:
    memory_inv m -∗
    l ↦ v ==∗
    memory_inv (delete l m) ∗ free l.
  Proof using Type.
    unseal.
    iIntros "(%f & Hm & Hf & %Hinv) Hl".
    iDestruct (ghost_map_lookup with "Hm Hl") as "%Hv".
    iMod (ghost_map_delete with "Hm Hl") as "Hm".
    iMod (gset_view_own_extend l with "Hf") as "[Hf Hfree]".
    { intros Hin. apply Hinv in Hin. by rewrite Hv in Hin. }
    iModIntro. iFrame.
    iPureIntro. intros l' Hin.
    rewrite elem_of_union elem_of_singleton in Hin.
    destruct Hin as [-> | Hin].
    - by apply lookup_delete_eq.
    - rewrite lookup_delete_ne; auto.
      intros ->. apply Hinv in Hin. by rewrite Hv in Hin.
  Qed.

End memory_laws.

Lemma memory_init `{!memGpreS Σ} m :
  ⊢ |==> ∃ _ : memGS Σ,
    memory_inv m ∗ ([∗ map] l ↦ v ∈ m, pointsto l (DfracOwn 1) v).
Proof.
  iMod (ghost_map_alloc m (K:=loc) (V:=val)) as (heap_name) "[Hm Hl]".
  iMod (gset_view_own_alloc_empty (A := loc)) as (free_name) "Hf".
  iExists (MemGS Σ heap_name free_name).
  unseal. simpl. iFrame.
  iPureIntro. discriminate.
Qed.
