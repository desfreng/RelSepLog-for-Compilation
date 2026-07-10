From RSL Require Import Prelude.

From RSL.Logic Require Import MemoryInv.

(* Class memGpreS Σ := *)
(*   MemGpreS { *)
(*       (* mem_pre_heapG :: ghost_mapG Σ loc val; *) *)
(*       (* mem_pre_freedG :: gset_viewG Σ loc; *) *)

(*       (* sim_pre_bijG :: gset_bijG Σ loc loc; *) *)
(*       (* sim_pre_expl_bijG :: expl_mapG Σ loc loc; *) *)
(*     }. *)

(* Class memGS Σ := *)
(*   MemGS { *)
(*       (* mem_heap_name : gname; *) *)
(*       (* mem_heapG :: ghost_mapG Σ loc val; *) *)

(*       (* mem_freed_name : gname; *) *)
(*       (* mem_freedG :: gset_viewG Σ loc; *) *)

(*       (* sim_mem_src_freed_name : gname; *) *)
(*       (* sim_mem_src_freed_G :: gset_viewG Σ loc; *) *)

(*       (* sim_bij_name : gname; *) *)
(*       (* sim_bijG :: gset_bijG Σ loc loc; *) *)

(*       (* sim_expl_name : gname; *) *)
(*       (* sim_explG :: expl_mapG Σ loc loc; *) *)
(*     }. *)


(*       (* gset_bijΣ loc loc; *) *)
(*       (* expl_mapΣ loc loc *) *)


(*   Definition src_freed (l : loc) : iProp Σ := *)
(*     gset_view_own_elem sim_mem_src_freed_name l. *)

(*   Definition src_freed_auth (fs : gset loc) : iProp Σ := *)
(*     gset_view_own_auth sim_mem_src_freed_name (DfracOwn 1%Qp) fs. *)


  (* Definition heap_bij_auth (L : gset (loc * loc)) : iProp Σ := *)
  (*   gset_bij_own_auth sim_bij_name (DfracOwn 1) L. *)

  (* Definition heap_bij_elem (lt ls : loc) : iProp Σ := *)
  (*   gset_bij_own_elem sim_bij_name lt ls. *)


  (* Definition expl_map_auth (expl : gmap loc loc) : iProp Σ := *)
  (*   expl_map_auth sim_expl_name expl. *)

  (* Definition expl_map_view (expl : gmap loc loc) : iProp Σ := *)
  (*   expl_map_frag sim_expl_name expl. *)

(* Notation "lt ⋈ ls" := (heap_bij_elem lt ls) (at level 20) : bi_scope. *)
(* Notation "↯ s" := (expl_map_view s) (at level 20) : bi_scope. *)

(* Section bij_law. *)
(*   Context `{!simGS Σ}. *)

(*   Global Instance bij_elem_persistent lt ls: Persistent (lt ⋈ ls). *)
(*   Proof using Type. apply _. Qed. *)

(*   Search (Decision (_ ∈ _)). *)
(*   Definition bij_inv (escaped: gmap loc loc) (val_rel : val -> val -> iProp Σ) := *)
(*     (∃ L, *)
(*         heap_bij_auth L ∗ *)
(*         [∗ set] '(lt, ls) ∈ L, *)
(*           if bool_decide (ls ∈ dom escaped) *)
(*           then ⌜True⌝ *)
(*           else (∃ vt vs, lt →ₜ vt ∗ ls →ₛ vs ∗ val_rel vt vs) *)
(*     )%I. *)

(*   Lemma bij_agree lt1 lt2 ls1 ls2: *)
(*     lt1 ⋈ ls1 -∗ lt2 ⋈ ls2 -∗ ⌜lt1 = lt2 <-> ls1 = ls2⌝. *)
(*   Proof using Type. *)
(*     iIntros "H1 H2". *)
(*     iApply (gset_bij_own_elem_agree with "H1 H2"). *)
(*   Qed. *)

(*   Lemma bij_agree_r lt ls1 ls2: *)
(*     lt ⋈ ls1 -∗ lt ⋈ ls2 -∗ ⌜ls1 = ls2⌝. *)
(*   Proof using Type. *)
(*     iIntros "H1 H2". *)
(*     iPoseProof (bij_agree with "H1 H2") as "<-". done. *)
(*   Qed. *)

(*   Lemma bij_agree_l lt1 lt2 ls: *)
(*     lt1 ⋈ ls -∗ lt2 ⋈ ls -∗ ⌜lt2 = lt1⌝. *)
(*   Proof using Type. *)
(*     iIntros "H1 H2". *)
(*     iPoseProof (bij_agree with "H2 H1") as "->". done. *)
(*   Qed. *)

(*   Lemma bij_access escaped val_rel lt ls: *)
(*     ls ∉ dom escaped -> *)
(*     bij_inv escaped val_rel -∗ *)
(*     lt ⋈ ls -∗ *)
(*     ∃ vt vs, *)
(*       lt →ₜ vt ∗ *)
(*       ls →ₛ vs ∗ *)
(*       val_rel vt vs ∗ *)
(*       (∀ vt' vs', *)
(*          lt →ₜ vt' -∗ *)
(*          ls →ₛ vs' -∗ *)
(*          val_rel vt' vs' -∗ *)
(*          bij_inv escaped val_rel). *)
(*   Proof using Type. *)
(*     iIntros (Hesc) "Hinv Hrel". *)
(*     rewrite <-(bool_decide_eq_false (_ ∈ _)) in Hesc. *)
(*     iDestruct "Hinv" as (L) "[Hauth Hheap]". *)
(*     iPoseProof (gset_bij_elem_of with "Hauth Hrel") as "%". *)
(*     iPoseProof (big_sepS_delete with "Hheap") as "[He Hinv]"; first done. *)
(*     simpl. rewrite Hesc. *)
(*     iDestruct "He" as (vt vs) "(Ht & Hs & Hvrel)". *)
(*     iExists vt, vs. iFrame. *)
(*     iIntros (vt' vs') "Ht Hs Hvrel". *)
(*     iExists L. iFrame. *)
(*     iApply big_sepS_delete; first done. *)
(*     simpl. rewrite Hesc. *)
(*     by iFrame. *)
(*   Qed. *)

(*   Lemma bij_insert escaped val_rel lt ls vt vs: *)
(*     ls ∉ dom escaped -> *)
(*     bij_inv escaped val_rel -∗ *)
(*     lt →ₜ vt -∗ *)
(*     ls →ₛ vs -∗ *)
(*     val_rel vt vs ==∗ *)
(*     bij_inv escaped val_rel ∗ lt ⋈ ls. *)
(*   Proof using Type. *)
(*     iIntros (Hesc) "Hinv Ht Hs Hrel". iDestruct "Hinv" as (L) "[Hauth Hheap]". *)
(*     rewrite <-(bool_decide_eq_false (_ ∈ _)) in Hesc. *)
(*     iAssert ((¬ ⌜set_Exists (λ '(lt', ls'), ls = ls') L⌝)%I) as "%Hexts". *)
(*     { iIntros (([lt' ls'] & Hin & <-)). *)
(*       iPoseProof (big_sepS_elem_of with "Hheap") as "H"; first done. *)
(*       simpl. rewrite Hesc. *)
(*       iDestruct "H" as (vt' vs') "(_ & Hcon & _)". *)
(*       iApply (source_mapsto_valid_2 with "Hs"). done. *)
(*     } *)

(*     iMod ((gset_bij_own_extend lt ls) with "Hauth") as "[Hinv #Helem]". *)
(*     - intros ls' Hls'. apply Hextt. by exists (lt, ls'). *)
(*     - intros lt' Hlt'. apply Hexts. by exists (lt', ls). *)
(*     - iModIntro. iSplitL; last done. *)
(*       iExists ({[(lt, ls)]} ∪ L)%I. iFrame. *)
(*       iApply big_sepS_insert. *)
(*       + contradict Hextt. by exists (lt, ls). *)
(*       + by iFrame. *)
(*   Qed. *)

(* End bij_law. *)
