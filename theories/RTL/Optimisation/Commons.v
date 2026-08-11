From RSL Require Import Prelude.

From RSL.RTL Require Import RTL.

Definition name_identical o : Prop := ∀ f, rtl_fn_name f = rtl_fn_name (o f).

Lemma opt_no_dup {Ps o} (Ho: name_identical o):
  is_no_dup (rtl_fn_name <$> prog_fun_list Ps) = true ->
  is_no_dup (rtl_fn_name <$> fmap o (prog_fun_list Ps)) = true.
Proof using Type.
  rewrite !is_no_dup_sound.
  induction (prog_fun_list Ps) as [ | f l IH ].
  - done.
  - simpl. intros H. inv H as [| ? ? HnIn HnDup].
    constructor; auto.
    intros (? & Heq & (f' & -> & H)%list_elem_of_fmap)%list_elem_of_fmap.
    apply HnIn. rewrite Ho, Heq.
    apply list_elem_of_fmap.
    by exists f'.
Qed.

Lemma opt_fun_list {Ps o} (Ho: name_identical o) fn f:
  find_fun_in_list (prog_fun_list Ps) fn = Some f ->
  find_fun_in_list (o <$> prog_fun_list Ps) fn = Some (o f).
Proof using Type.
  unfold find_fun_in_list.
  intros ([? f'] & H & Heq)%fmap_Some. simpl in Heq. subst f'.
  apply list_find_Some in H as (Hres & Hp & Hfirst).
  rewrite fmap_Some. eexists (_, _). split; last reflexivity.
  apply list_find_Some. split_and!.
  - apply list_lookup_fmap_Some. by eexists.
  - by rewrite <-Ho.
  - intros j ? (f' & -> & Hin)%list_lookup_fmap_Some Hj. simpl.
    rewrite <-Ho. by eapply Hfirst.
Qed.

Lemma opt_main_some {Ps o} (Ho: name_identical o):
  is_Some (find_fun_in_list (prog_fun_list Ps) (prog_main Ps)) ->
  is_Some (find_fun_in_list (o <$> prog_fun_list Ps) (prog_main Ps)).
Proof using Type. intros [f H]. eexists. by apply opt_fun_list. Qed.
