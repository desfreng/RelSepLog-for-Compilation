From RSL Require Import Prelude.

From Coinduction Require Import tower.

From RSL.RTL Require Import RTL Semantics.
From RSL.Simulations Require Import FreeSim.

Section CallBindLemma.
  Context {I J: WfRel}.
  Context {Pt Ps : prog rtl_lang} {C : Chain (fsim_lfp J I Pt Ps)}.

  Context (ct : list stackframe) (ft : rtl_function) (pct : node) (ρt : regbank).
  Context (j: J) (i: I).
  Context (cs : list stackframe) (fs : rtl_function) (pcs : node) (ρs : regbank).
  Context (Q : val -> val -> rProp).

  Lemma fsim_lfp_rtl_call_bind {Hj: HasSucc j} {Hi: HasSucc i} P1 P2 dstt dsts pct' pcs' fnt fns valt vals mt ms:
    fsim_lfp _ _ Pt Ps (elem C) P1
      ([], CallState fnt valt, mt) j i ([], CallState fns vals, ms) ->
    (∀ j' i' vt vs mt' ms',
       j ⊏ j' ->
       i ⊏ i' ->
       P1 (vt, mt') (vs, ms') ->
       fsim_lfp _ _ Pt Ps (elem C) P2
         (ct, State ft pct' (⟦dstt ⇐ vt⟧ ρt), mt') j' i'
         (cs, State fs pcs' (⟦dsts ⇐ vs⟧ ρs), ms')) ->
    fsim_lfp _ _ Pt Ps (elem C) P2
      (Stackframe dstt ft pct' ρt :: ct, CallState fnt valt, mt) j i
      (Stackframe dsts fs pcs' ρs :: cs, CallState fns vals, ms).
  Proof using Type.
    set (Σt := Stackframe dstt ft pct' ρt :: ct).
    set (Σs := Stackframe dsts fs pcs' ρs :: cs).
    assert
      (Hgen :
        ∀ t jc ic s,
         fsim_lfp _ _ Pt Ps (elem C) P1 t jc ic s ->
         ∀ σt pst mtt σs pss mss,
         (∀ j' i' vt vs mt' ms',
            j ⊏ j' ->
            i ⊏ i' ->
            P1 (vt, mt') (vs, ms') ->
            fsim_lfp _ _ Pt Ps (elem C) P2
              (ct, State ft pct' (⟦ dstt ⇐ vt ⟧ ρt), mt') j' i'
              (cs, State fs pcs' (⟦ dsts ⇐ vs ⟧ ρs), ms')) ->
         t = (σt, pst, mtt) ->
         s = (σs, pss, mss) ->
         fsim_lfp _ _ Pt Ps (elem C) P2
           (σt ++ Σt, pst, mtt) jc ic (σs ++ Σs, pss, mss)).
    { apply tower.
      { clear.
        apply inf_closed_all. intros t.
        apply inf_closed_all. intros jc.
        apply inf_closed_all. intros ic.
        apply inf_closed_all. intros s.
        apply inf_closed_impl.
        { intros P P' H HP. by apply H, HP. }
        apply inf_closed_all. intros σt.
        apply inf_closed_all. intros pst.
        apply inf_closed_all. intros mtt.
        apply inf_closed_all. intros σs.
        apply inf_closed_all. intros pss.
        apply inf_closed_all. intros mts.
        apply inf_closed_impl.
        { intros P P' H HP. repeat intro. by apply H, HP. }
        apply inf_closed_impl. { by repeat intro. }
        apply inf_closed_impl. { by repeat intro. }
        intros P Hp P' H. eapply (Hp _ H).
      }
      clear C mt ms.
      intros C CIH t jc ic s Hsim.
      induction Hsim as
        [ t jc ic s Hfin
        | t jc ic s Hstuck
        | t jc ic' ic s s' Hstep Hsim IH
        | t jc ic s Hprog Ht
        | t jc jc' ic ic' s Htt Hss Hgfp ];
        intros σt pst mt σs pss ms Hcont -> ->.
      - destruct Hfin as ([vt mt'] & [vs ms'] & Hfint & Hfins & Hphi).
        apply is_final_struct in Hfint; injection Hfint as -> -> ->.
        apply is_final_struct in Hfins; injection Hfins as -> -> ->.
        apply FTargetSteps. { by apply ret_can_progress. }
        intros t' Hstept'. inv Hstept'.
        exists (succ j).
        eapply FSourceSteps with (i' := succ i). { by econstructor. }
        by apply Hcont, Hphi; apply is_succ.
      - apply FSourceStuck. by apply unlift_stuck.
      - destruct s' as [[? ?] ?].
        eapply FSourceSteps. { by apply lift_step. }
        by apply IH.
      - apply FTargetSteps. { by apply lift_can_progress. }
        intros t'' Hstep''.
        assert (Hnfin: is_final ((σt, pst, mt) : state rtl_lang) = None).
        { by eapply progress_not_final. }
        edestruct (step_frame_preserved _ _ _ _ _ _ Hnfin Hstep'')
          as (σt' & pt' & mt'' & -> & Hstept').
        destruct (Ht _ Hstept') as (jc' & Hsim' & IH').
        exists jc'. by apply IH'.
      - eapply FProgress.
        + eassumption.
        + eassumption.
        + eapply CIH; eauto. repeat intro.
          by eapply (b_chain C), Hcont.
    }
    intros Hcont Hcall.
    change (Σs) with ([] ++ Σs).
    change (Σt) with ([] ++ Σt).
    by eapply Hgen.
  Qed.

End CallBindLemma.
