From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations Require Import Free.

Section SimCompose.
  Context {Λt Λm Λs: lang}.
  Context (Et: genv Λt) (Em: genv Λm) (Es: genv Λs).
  Context (Jt Im Jm Is : WfRel).
  Context (ϕ: post Λt Λm) (ψ: post Λm Λs).

  Let J : WfRel := WfDoubled Jt.
  Let I : WfRel := WfDoubled Is.
  Let ξ : post Λt Λs := compose_post ϕ ψ.

  Abbreviation fsim_tm := (fsim Jt Im Et Em ϕ).
  Abbreviation fsim_ms := (fsim Jm Is Em Es ψ).

  Abbreviation fsim := (fsim J I Et Es ξ).
  Abbreviation fsim_lfp := (fsim_lfp J I Et Es).

  Implicit Type (R: Chain fsim_lfp).

  Definition Inv R :=
    ∀ m j_m i_s s,
    fsim_ms m j_m i_s s ->
    ∀ t j_t i_m,
    fsim_tm t j_t i_m m ->
    ∀ j i, Low j_t ⊑ j -> Low i_s ⊑ i -> elem R ξ t j i s.

  Lemma final_ms R :
    ∀ t j_t i_m m,
    fsim_tm t j_t i_m m ->
    ∀ s,
    both_final ψ m s ->
    ∀ j i, fsim_lfp (elem R) ξ t j i s.
  Proof using Type.
    (* m is final. *)
    (* This means that t ~ m will end up and a both final. *)
    (* So, we can state the t ~ s simulation for any indices. *)
    intros t j_t i_m.
    revert t j_t.
    (* i_m can only decrease, m is final. So induction on it. *)
    induction i_m as [i_m IHim] using (well_founded_induction wf).
    intros t j_t m Htm%fsim_unroll.
    induction Htm as [ t j_t i_m m Hfinal_tm
                     | t j_t i_m m Hstuck_m
                     | t j_t i_m i_m' m m' Hm Htm IHs
                     | t j_t i_m m Hprog_t IHt
                     | t j_t j_t' i_m i_m' m Hj Hi Htm ]; intros s Hfinal_ms j i.
    - (* Both Final -> This is the base case, t is final too *)
      by eapply FRelated, compose_final.
    - (* Source Stuck -> impossible, s is supposed final *)
      by langmixin.
    - (* Source Steps -> impossible, s is supposed final *)
      by langmixin.
    - (* Target Steps -> t steps and then we use the induction hyp on the sim *)
      apply FTargetSteps. { done. }
      intros t' Ht.
      specialize (IHt _ Ht) as (j_t' & Htm & IH).
      exists j. by apply IH.
    - (* Indices Comsumption. *)
      (* This causes i_m to decrease. *)
      (* It can only happen a finite time as m is final. *)
      (* So we use the induction hyp on the decreasing index. *)
      by eapply IHim.
  Qed.

  Lemma stuck_m R :
    ∀ m j_m i_s s,
    fsim_ms m j_m i_s s ->
    super_stuck Em m ->
    ∀ t j i, fsim_lfp (elem R) ξ t j i s.
  Proof using Type.
    (* m is stuck -> so must be s at some point *)
    intros m j_m.
    revert m.
    (* Because m is stuck, j_m can only decrease -> induction on it *)
    induction j_m as [j_m IHjm] using (well_founded_induction wf).
    intros m i_s s Hms%fsim_unroll.
    (* Next induction on the simulation Hms to make s stuck *)
    induction Hms as [ m j_m i_s s Hfinal_ms
                     | m j_m i_s s Hstuck_s
                     | m j_m i_s i_s' s s' Hs Hms IHs
                     | m j_m i_s s Hprog_m IHm
                     | m j_m j_m' i_s i_s' s Hj Hi Hms ];
      intros Hstuck_m t j i.
    - (* m and s final -> impossible *)
      by langmixin.
    - (* s is stuck -> use source stuck *)
      by apply FSourceStuck.
    - (* s steps -> use IH on it *)
      eapply FSourceSteps with (i' := Low i_s'). { done. }
      by apply IHs.
    - (* m steps -> impossible *)
      by langmixin.
    - (* Index comsumption -> j_m decrease, we use IHjm *)
      by eapply IHjm.
  Qed.

  Lemma final_tm R :
    ∀ m j_m i_s s,
    fsim_ms m j_m i_s s ->
    ∀ t,
    both_final ϕ t m ->
    ∀ j i, fsim_lfp (elem R) ξ t j i s.
  Proof using Type.
    (* t and m are final. So s must finish (final or stuck at some point) *)
    intros m j_m.
    revert m.
    (* Because t and m are final, j_m can only decrease -> induction on it *)
    induction j_m as [j_m IHjm] using (well_founded_induction wf).
    intros m i_s s Hms%fsim_unroll.
    (* Next induction on the simulation Hms to make s finish *)
    induction Hms as [ m j_m i_s s Hfinal_ms
                     | m j_m i_s s Hstuck_s
                     | m j_m i_s i_s' s s' Hs Hms IHs
                     | m j_m i_s s Hprog_m IHm
                     | m j_m j_m' i_s i_s' s Hj Hi Hms ];
      intros t Hfinal_tm j i .
    - (* s is final -> we can close the sim *)
      by eapply FRelated, compose_final.
    - (* s is stuck -> we close the sim by source stuck *)
      by apply FSourceStuck.
    - (* s steps -> we use IHs *)
      eapply FSourceSteps with (i' := Low i_s'). { done. }
      by apply IHs.
    - (* m steps -> Impossible it's final *)
      by langmixin.
    - (* Index comsumption -> j_m decrease, we use IHjm *)
      by eapply IHjm.
  Qed.

  Lemma progress_from_t R (CIH: Inv R) :
    ∀ m s j_m i_s,
    fsim_ms m j_m i_s s ->
    ∀ t j_t i_m ,
    fsim_tm t j_t i_m m ->
    ∀ j i, Low j_t ⊏ j -> Low i_s ⊑ i -> fsim_lfp (elem R) ξ t j i s.
  Proof using Type.
    (* t has made some progress (Low j_t ⊏ j) *)
    (* So either: *)
    (* - s make some progress through m, we can then use the CIH *)
    (* - s stucks *)
    (* - s and m are final, t must terminate (by final_tm) *)
    intros m s j_m i_s Hms%fsim_unroll.
    induction Hms as
      [ m j_m i_s s Hfinal_ms
      | m j_m i_s s Hstuck_s
      | m j_m i_s i_s' s s' Hs Hms IHs
      | m j_m i_s s Hprog_m IHm
      | m j_m j_m' i_s i_s' s Hj Hi Hms ].
    - (* m and s are final, so t must be too *)
      intros t j_t i_m Htm j i _ _.
      by eapply final_ms.
    - (* s is Stuck -> trivial by Source Stuck *)
      intros t j_t i_m Htm j i _ _. by apply FSourceStuck.
    - (* s Steps *)
      intros t j_t i_m Htm j i Hlow_j Hlow_i.
      eapply FSourceSteps. { done. }
      (* Because we assumed that t has already made some progress (ie Hlow_j) *)
      (* We can close the goal using an index consumption, and then the coinductive Hyp *)
      eapply FProgress.
      + done.
      + by apply low_high.
      + eapply CIH; done || by apply fsim_roll.
    - (* m steps. *)
      (* Because m can step, t must step at some point. *)
      intros t j_t i_m Htm.
      revert t j_t m Htm s i_s Hprog_m IHm.
      (* Induction on the index of m in Htm *)
      induction i_m as [i_m IHim] using (well_founded_induction wf).
      intros t j_t m Htm%fsim_unroll.
      (* Induction on the simulation Hmt *)
      induction Htm as [ t j_t i_m m Hfinal_tm
                       | t j_t i_m m Hstuck_m
                       | t j_t i_m i_m' m m' Hm Htm _
                       | t j_t i_m m Hprog_t IHt
                       | t j_t j_t' i_m i_m' m Hj Hi Htm ];
        intros s i_s Hprog IHm j i Hlow_j Hlow_i.
      + (* m and t final -> Impossible here, m can progress *)
        by langmixin.
      + (* m stuck -> Impossible here, m can progress *)
        by langmixin.
      + (* m is stepping in t ~ m *)
        (* We can match this progress in m ~ s using IHm *)
        specialize (IHm _ Hm) as (_ & _ & IHm).
        eapply IHm; eauto. by apply fsim_roll.
      + (* t finally steps *)
        eapply FTargetSteps. { done. }
        intros t' Ht.
        specialize (IHt _ Ht) as (j_t' & Htm & IHt).
        (* We use the index in IHt, but we use it as High *)
        eexists. eapply IHt; eauto. by apply low_high.
      + (* Here the index of m decrease. *)
        (* We use the IH on it to get to a target step *)
        eapply IHim; eauto.
        etransitivity; eauto. by constructor.
    - (* Index consumption -> we can use CIH *)
      intros t j_t i_m Htm j i Hlow_j Hlow_i.
      eapply FProgress.
      + done.
      + eapply lt_from_lt_le; last done. by constructor.
      + by eapply CIH.
  Qed.

  Lemma progress_from_s R (CIH: Inv R) :
    ∀ t j_t i_m m,
    fsim_tm t j_t i_m m ->
    ∀ s j_m i_s,
    fsim_ms m j_m i_s s ->
    ∀ j i, Low j_t ⊑ j -> Low i_s ⊏ i -> fsim_lfp (elem R) ξ t j i s.
  Proof using Type.
    (* s has made some progress (Low i_s ⊏ i) *)
    (* By induction on t ~ m, either: *)
    (* - t and m are final, s can terminate *)
    (* - s make some progress through m, we can then use the CIH *)
    (* - m stucks and so must s *)
    intros t j_t i_m m Htm%fsim_unroll.
    induction Htm as [ t j_t i_m m Hfinal_tm
                     | t j_t i_m m Hstuck_m
                     | t j_t i_m i_m' m m' Hm _ IHm
                     | t j_t i_m m Hprog_t IHt
                     | t j_t j_t' i_m i_m' m Hj Hi Htm ].
    - intros s j_m i_s Hms j i _ _. by eapply final_tm.
    - (* m is stuck -> so must be s at some point *)
      intros s j_m i_s Hms j i _ _. by eapply stuck_m.
    - (* m steps. *)
      (* Because m can step, s must step or be stuck at some point. *)
      intros s j_m i_s Hms.
      revert m i_s s Hms m' Hm IHm.
      (* Induction on the index of m *)
      induction j_m as [j_m IHjm] using (well_founded_induction wf).
      intros m i_s s Hms%fsim_unroll.
      (* Induction on simulation m ~ s *)
      induction Hms as [ m j_m i_s s Hfinal_ms
                       | m j_m i_s s Hstuck_s
                       | m j_m i_s i_s' s s' Hs Hms IHs
                       | m j_m i_s s Hprog_m IH
                       | m j_m j_m' i_s i_s' s Hj Hi Hms ];
        intros m' Hm IHm j i Hlow_j Hlow_i.
      + (* m and s final -> impossible, m can progress *)
        by langmixin.
      + (* s stuck -> we close it by FSourceStuck *)
        by apply FSourceStuck.
      + (* s finally steps. *)
        eapply FSourceSteps. { done. }
        eapply IHs; eauto. by apply low_high.
      + (* m is stepping in m ~ s *)
        (* We can match this progress in t ~ m using IHm *)
        specialize (IH _ Hm) as (j_m' & Hms & _).
        eapply IHm; eauto. by apply fsim_roll.
      + (* Here the index of m decrease. *)
        (* We use the IH on it to get to a target step *)
        eapply IHjm; eauto.
        etransitivity; eauto. by constructor.
    - (* t steps *)
      intros s j_m i_s Hms j i Hlow_j Hlow_i.
      apply FTargetSteps. { done. }
      intros t' Ht.
      specialize (IHt _ Ht) as (j_t' & Htm & IHt).
      (* Because we assumed that i has already made some progress (ie Hlow_i) *)
      (* We can close the goal using an index consumption, and then the coinductive Hyp *)
      eexists. eapply FProgress.
      + by apply low_high.
      + done.
      + eapply CIH; done || by apply fsim_roll.
    - (* Index consumption. *)
      intros s j_m i_s Hms j i Hlow_j Hlow_i.
      eapply FProgress.
      + eapply lt_from_lt_le; last done. by constructor.
      + done.
      + by eapply CIH.
  Qed.

  Lemma fsim_compose_inv :
    ∀ m j_m i_s s,
    fsim_ms m j_m i_s s ->
    ∀ t j_t i_m,
    fsim_tm t j_t i_m m ->
    ∀ j i, Low j_t ⊑ j -> Low i_s ⊑ i -> fsim t j i s.
  Proof using Type.
    (* Coinduction on the hyp. *)
    unfold fsim at 3.
    coinduction R CIH.
    (* Induction on the m ~ s simulation. *)
    intros m j_m i_s s Hms%fsim_unroll.
    induction Hms as [ m j_m i_s s Hfinal_ms
                     | m j_m i_s s Hstuck_s
                     | m j_m i_s i_s' s s' Hs IHs
                     | m j_m i_s s Hprog_m IHm
                     | m j_m j_m' i_s i_s' s Hj Hi Hms ];
      intros t j_t i_m Htm i j Hlow_j Hlow_i.
    - (* m and s are final, so t must be too. *)
      by eapply final_ms.
    - (* s is stuck -> use FSourceStuck. *)
      by apply FSourceStuck.
    - (* s steps *)
      eapply FSourceSteps. { done. }
      (* We enter the s leading mode. *)
      (* The progress index is set to High *)
      eapply progress_from_s; eauto using low_high.
      by apply fsim_roll.
    - (* m steps *)
      (* We first build back the original simulation *)
      assert (fsim_ms m j_m i_s s) as Hms. {
        eapply fsim_roll, FTargetSteps. { done. }
        intros m' Hm.
        specialize (IHm _ Hm) as (j_m' & Hms & _).
        by exists j_m'.
      }
      (* Then, lets look on how Htm is made. *)
      apply fsim_unroll in Htm.
      destruct Htm as [ t j_t i_m m Hfinal_tm
                      | t j_t i_m m Hstuck_m
                      | t j_t i_m i_m' m m' Hm Htm
                      | t j_t i_m m Hprog_t Htm
                      | t j_t j_t' i_m i_m' m Hj Hi Htm ].
      + (* t and m are final -> impossible m can step. *)
        by langmixin.
      + (* m is stuck -> impossible m can step. *)
        by langmixin.
      + (* m steps -> we can use the induction hyp on m *)
        specialize (IHm _ Hm) as (j_m' & _ & IHm).
        eapply IHm; eauto. by apply fsim_roll.
      + (* t steps. *)
        apply FTargetSteps. { done. }
        intros t' Ht. destruct (Htm _ Ht) as (j_t' & Htm').
        (* We enter t leading mode *)
        (* The progress index is set to High *)
        eexists. eapply progress_from_t; eauto using low_high.
        by apply fsim_roll.
      + (* We can enter t leading mode *)
        eapply progress_from_t; eauto.
        eapply lt_from_lt_le; eauto. by constructor.
    - (* We can enter s leading mode *)
      eapply progress_from_s; eauto.
      eapply lt_from_lt_le; eauto. by constructor.
  Qed.

  Theorem fsim_compose t m s :
    ∀ j_t i_m j_m i_s,
    fsim_tm t j_t i_m m ->
    fsim_ms m j_m i_s s ->
    fsim t (Low j_t) (Low i_s) s.
  Proof using Type. intros. by eapply fsim_compose_inv. Qed.

End SimCompose.
