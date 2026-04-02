From Stdlib Require Import Utf8.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.Relations.

From RSL Require Import NatMap.
From RSL Require Import RTL.
From RSL Require Import Notations.
From RSL Require Import Semantics.
From RSL Require Import Tactics.
From RSL Require Import WP.

Import RTLNotations.
Import ListNotations.

Section WPNaive.
  Variable P: program.

  Fixpoint wp_ (fuel: nat) (f: function) (pc: node) (Q: postcondition)
    : regmap * memory -> Prop :=
    match fuel with
    | O => fun '(ρ, m) => False
    | S n =>
        match NatMap.find pc f.(fn_code) with
        | Some <{ nop -> pc }> =>
            wp_ n f pc Q

        | Some <{ dst := @ op args -> pc }> =>
            fun '(ρ, m) =>
              ∃ v,
                eval_op op (get_regs ρ args) = Some v ∧
                wp_ n f pc Q (set_reg ρ dst v, m)

        | Some <{ dst := ! src -> pc }> =>
            fun '(ρ, m) =>
              let addr := get_reg ρ src in
              ∃ v, get_at m addr = Some v ∧
                   wp_ n f pc Q (set_reg ρ dst v, m)

        | Some <{ ! dst := src -> pc }> =>
            fun '(ρ, m) =>
              let addr := get_reg ρ dst in
              let v := get_reg ρ src in
              ∃ m', set_at m addr v = Some m' ∧
                    wp_ n f pc Q (ρ, m')

        | Some <{ if cond then goto pc1 else goto pc2 }> =>
            fun '(ρ, m) =>
              if (get_reg ρ cond =? 0)%Z
              then wp_ n f pc1 Q (ρ, m)
              else wp_ n f pc2 Q (ρ, m)

        | Some <{ ret r }> =>
            fun '(ρ, m) => Q (get_reg ρ r) m

        | Some <{ dst := @call sig args -> pc }> =>
            fun '(ρ, m) =>
              ∃ fn Pre Post,
                let vals := get_regs ρ args in
                find_fun P sig = Some fn ∧
                hoare P Pre fn Post ∧
                Pre vals m ∧
                ∀ v m', let ρ' := set_reg ρ dst v in
                        Post v m' -> wp_ n f pc Q (ρ', m')
        | None =>
            fun σ => False
        end
    end.

  Lemma wp_sound: ∀ fuel f pc Q ρ m,
    wp_ fuel f pc Q (ρ, m) -> wp P f pc Q (ρ, m).
  Proof.
    induction fuel as [ | n IH ].
    - easy.
    - simpl. intros f pc Q σ H Hwp.
      destruct (NatMap.find pc (fn_code f)) as [[] | ] eqn:Hi.
      + eapply wp_nop; eauto.
      + eapply wp_op; eauto.
        destruct Hwp as (v & Hv & Hwp); eauto.
      + eapply wp_load; eauto.
        destruct Hwp as (v & Hv & Hwp); eauto.
      + eapply wp_store; eauto.
        destruct Hwp as (m' & Hm' & Hwp); eauto.
      + eapply wp_call; eauto.
        destruct Hwp as (fn & Pre & Post & Hfun & Hspec & Hpre & Hwp).
        exists fn. exists Pre. exists Post. repeat split; eauto.
      + eapply wp_cond; eauto.
        destruct (get_reg σ r =? 0)%Z; auto.
      + eapply wp_ret. apply Hi. auto.
      + contradiction.
  Qed.
End WPNaive.

Section WPGenerator.
  Variable P : program.

  Definition node_inv : Type := node -> regmap * memory -> Prop.

  Record inv_sound (f : function) (I : node_inv) (Q : postcondition) : Prop :=
  {
    sound_ret : ∀ pc v,
      f@pc is <{ ret v }> ->
      ∀ ρ m, I pc (ρ, m) -> Q (get_reg ρ v) m

  ; sound_nop : ∀ pc pc',
      f@pc is <{ nop -> pc' }> ->
      ∀ ρ m, I pc (ρ, m) -> I pc' (ρ, m)

  ; sound_op : ∀ pc dst op args pc',
      f@pc is <{ dst := @op args -> pc' }> ->
      ∀ ρ m, I pc (ρ, m) ->
             ∃ v,
               eval_op op (get_regs ρ args) = Some v
               ∧ I pc' (set_reg ρ dst v, m)

  ; sound_load : ∀ pc dst src pc',
      f@pc is <{ dst := !src -> pc' }> ->
      ∀ ρ m, I pc (ρ, m) ->
             ∃ v,
               get_at m (get_reg ρ src) = Some v
               ∧ I pc' (set_reg ρ dst v, m)

  ; sound_store : ∀ pc dst src pc',
      f@pc is <{ !dst := src -> pc' }> ->
      ∀ ρ m, I pc (ρ, m) ->
             ∃ m',
               set_at m (get_reg ρ dst) (get_reg ρ src) = Some m'
               ∧ I pc' (ρ, m')

  ; sound_cond : ∀ pc cond ifso ifnot,
      f@pc is <{ if cond then goto ifso else goto ifnot }> ->
      ∀ ρ m, I pc (ρ, m) ->
             if (get_reg ρ cond =? 0)%Z
             then I ifso (ρ, m)
             else I ifnot (ρ, m)

  ; sound_call : ∀ pc dst sig args pc',
      f@pc is <{ dst := @call sig args -> pc' }> ->
      ∀ ρ m, I pc (ρ, m) ->
             ∃ fn Pre Post,
               find_fun P sig = Some fn
               ∧ hoare P Pre fn Post
               ∧ Pre (get_regs ρ args) m
               ∧ ∀ v m', Post v m' -> I pc' (set_reg ρ dst v, m')
  }.

End WPGenerator.
