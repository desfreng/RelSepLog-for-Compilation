From RSL Require Import Prelude.

From RSL.Language Require Export Language.
From RSL.Commons Require Export WfRel.

From Coinduction Require Import all.

Section CCSimDef.
  Context {Λt Λs: lang}.
  Context (W: WfRel) (Et: genv Λt) (Es: genv Λs) (ϕ: post Λt Λs).

  Variant ccsim_lfp' (gfp: W -> config Λt -> config Λs -> Prop)
    : W -> config Λt -> config Λs -> Prop :=
    | CCRelated : ∀ i t s s',
      Es ⊨ s ->>* s' ->
      both_final ϕ t s' ->
      ccsim_lfp' gfp i t s

    | CCStuck : ∀ i t s s',
      Es ⊨ s ->>* s' ->
      super_stuck Es s' ->
      ccsim_lfp' gfp i t s

    | CCProgress : ∀ i t s,
      can_progress Et t ->
      (∀ t',
         Et ⊨ t ->> t' ->
         (∃ i' s', i' ⊏ i ∧ Es ⊨ s ->>* s' ∧ gfp i' t' s')
         ∨
         (∃ i' s', Es ⊨ s ->>+ s' ∧ gfp i' t' s')) ->
      ccsim_lfp' gfp i t s.

  Program Definition ccsim_lfp : mon (element W -> config Λt -> config Λs -> Prop) :=
    {| body := ccsim_lfp' |}.
  Next Obligation.
    intros gfp gfp' Hgfp i t s Hsim.
    induction Hsim as [ i t s s' Hs Hfinal
                      | i t s s' Hs Hstuck
                      | i t s Hprog H ].
    - by econstructor.
    - by econstructor.
    - apply CCProgress. { done. }
      intros t' Ht.
      specialize (H _ Ht) as [(i' & s' & Hi & Hs & Hsim) | (i' & s' & Hs & Hsim)].
      + left. exists i', s'. split_and!; auto.
        now apply Hgfp.
      + right. exists i', s'. split_and!; auto.
        now apply Hgfp.
  Qed.

  Lemma ccsim_unroll i t s :
    gfp ccsim_lfp i t s -> ccsim_lfp' (gfp ccsim_lfp) i t s.
  Proof using Type. apply (gfp_fp ccsim_lfp). Qed.

  Lemma ccsim_roll i t s :
    ccsim_lfp' (gfp ccsim_lfp) i t s -> gfp ccsim_lfp i t s.
  Proof using Type. apply (gfp_fp ccsim_lfp). Qed.

  Definition ccsim  := gfp ccsim_lfp.

  Lemma ccsim_idx_mono (R: Chain ccsim_lfp):
    ∀ i t s,
    (elem R) i t s ->
    ∀ i',
    i ⊑ i' ->
    (elem R) i' t s.
  Proof using Type.
    apply tower.
    { intros P Hp i t s Hinf i' Hi.
      intros Q Hq. eapply (Hp _ Hq); try eassumption.
      now apply Hinf.
    }
    clear R. intros R CIH i t s Hsim.
    induction Hsim as [ i t s s' Hs Hfinal
                      | i t s s' Hs Hstuck
                      | i t s Hprog H ].
    - by econstructor.
    - by econstructor.
    - intros i' Hi.
      apply CCProgress. { done. }
      intros t' Ht.
      specialize (H _ Ht) as [(i'' & s' & Hi' & Hs & Hsim) | (i'' & s' & Hs & Hsim)].
      + left. eexists _, s'.
        split; [| by split].
        by eapply lt_from_lt_le.
      + right. by exists i'', s'.
  Qed.
End CCSimDef.
