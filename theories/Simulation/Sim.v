From RSL Require Import Prelude.

From Coinduction Require Import all.

(* Set Mangle Names. *)

Section SimDef.
  Context {Λₜ Λₛ: lang}.
  Context (Pₜ: prog Λₜ) (Pₛ: prog Λₛ) (Φ: value Λₜ -> value Λₛ -> Prop).

  Definition is_final (t: state Λₜ) (s: state Λₛ) : Prop :=
    ∃ vₜ vₛ, is_final t = Some vₜ ∧ is_final s = Some vₛ ∧ Φ vₜ vₛ.

  Inductive sim_lfp'
    (gfp: state Λₜ -> state Λₛ -> Prop) : state Λₜ -> state Λₛ-> Prop :=
  | BothFinal : ∀ t s,
    is_final t s -> sim_lfp' gfp t s

  | SourceStuck : ∀ t s,
    stuck Pₛ s -> sim_lfp' gfp t s

  | TargetStutter : ∀ t s s',
    Pₛ ⊨ s ->> s' -> sim_lfp' gfp t s' -> sim_lfp' gfp t s

  | TargetSteps : ∀ t s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> sim_lfp' gfp t' s) ->
    sim_lfp' gfp t s

  | BothSteps : ∀ t s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ s', Pₛ ⊨ s ->> s' ∧ gfp t' s') ->
    sim_lfp' gfp t s.

  Instance sim_lfp'_proper : Proper (leq ==> leq) sim_lfp'.
  Proof.
    intros gfp gfp' Hgfp s t H. induction H as [ | | | | ? ? ? H ];
      try (econstructor; eassumption || now apply Hlfp).
    apply BothSteps; eauto. intros t' Hstep.
    destruct (H _ Hstep) as (? & ? & ?).
    eexists. split; eassumption || now apply Hgfp.
  Qed.

  Definition sim_lfp : mon (state Λₜ -> state Λₛ -> Prop) := {| body := sim_lfp' |}.

  Lemma sim_unroll t s :
    gfp sim_lfp t s -> sim_lfp' (gfp sim_lfp) t s.
  Proof. apply (gfp_fp sim_lfp). Qed.

  Lemma sim_roll t s :
    sim_lfp' (gfp sim_lfp) t s -> gfp sim_lfp t s.
  Proof. apply (gfp_fp sim_lfp). Qed.

  Definition sim  := gfp sim_lfp.

  Notation "t '≲' s" :=
    (gfp sim_lfp t s)
      (at level 70).

  Lemma source_steps :
    ∀ s t s',
    Pₛ ⊨ s ->>* s' ->
    t ≲ s' ->
    t ≲ s.
  Proof.
    intros s t s' H.
    revert t.
    induction H as [ | s s' s'' Hs Hrtc IH ]; intros t H.
    - easy.
    - apply sim_roll.
      eapply TargetStutter.
      + eassumption.
      + apply sim_unroll. now apply IH.
  Qed.

  Lemma both_source_steps : ∀ t s,
    can_progress Pₜ t ->
    (∀ t', Pₜ ⊨ t ->> t' -> ∃ s', Pₛ ⊨ s ->>+ s' ∧ t'≲ s') ->
    t ≲ s.
  Proof.
    intros t s Hp H.
    apply sim_roll.
    apply BothSteps; auto.
    intros t' Ht.
    apply H in Ht. destruct Ht as (s'' & Hplus & Hsim).
    apply pstep_inv_l in Hplus.
    destruct Hplus as (s' & Hs & Hrtc).
    exists s'. split; auto.
    eapply source_steps; eassumption.
  Qed.

  Lemma target_final : ∀ t s s',
    Pₛ ⊨ s ->>* s' ->
    is_final t s' ->
    t ≲ s.
  Proof.
    intros t s s' H Hfin.
    apply source_steps with s'; auto.
    apply sim_roll. now constructor.
  Qed.

  Lemma source_will_stuck : ∀ t s s',
    Pₛ ⊨ s ->>* s' ->
    stuck Pₛ s' ->
    t ≲ s.
  Proof.
    intros t s s' H Hstuck.
    apply source_steps with s'; auto.
    apply sim_roll. now constructor.
  Qed.

  Lemma target_n_steps: ∀ t s n,
    (∀ j t', j < n -> Pₜ ⊨ t -{ j }> t' -> can_progress Pₜ t') ->
    (∀ t', Pₜ ⊨ t -{ n }> t' -> t' ≲ s) ->
    t ≲ s.
  Proof.
    intros t s n Hprog H.
    induction n as [ | n IH ] in t, H, Hprog |- *.
    - apply H. constructor.
    - apply sim_roll.
      apply TargetSteps.
      + apply Hprog with 0; lia || constructor.
      + intros t' Ht.
        apply sim_unroll.
        apply IH.
        * intros j t'' Hle Hp.
          apply Hprog with (1+j); try lia.
          econstructor; now eauto.
        * intros t'' Ht'. apply H.
          econstructor; now eauto.
  Qed.

End SimDef.
