From RSL Require Import Prelude.

From stdpp Require Import strings.

From RSL Require Import Commons.WP.
From RSL Require Import Commons.Logic.

From RSL Require Import RTL.RTL.
From RSL Require Import RTL.Semantics.
From RSL Require Import RTL.Notations.
From RSL Require Import RTL.WP.

Import RTLNotations.

Section Play.
  Let Λ : lang := rtl_lang.
  Context (P: prog Λ).

  Let x : reg := 0.
  Let one : reg := 1.
  Let ten : reg := 2.
  Let diff : reg := 3.

  Definition NodeInv Q f pc (NI : logic) : Prop := ⊢ NI -> wp P Q f pc.

  Definition test : function :=
    {|
      fn_name := "test"%string;
      fn_regs := [];
      fn_entrypoint := 0;
      fn_code := <{{
            0: x := #0 -> 1;
            1: one := #1 -> 2;
            2: ten := #10 -> 3;
            3: diff := ten - x -> 4;
            4: if diff then goto 6 else goto 5;
            5: x := x + one -> 3;
            6: ret x;
        }}>;
      fn_regs_no_dup := eq_refl;
    |}.

  Ltac step lemma :=
    match goal with
    | |- wp _ _ ?f ?pc _ _ ?n =>
        let H := fresh "Hpc" in
        eassert (H: f@pc is _) by reflexivity;
        eapply lemma;
        [now apply H|];
        clear H; repeat split; simpl_reg; unfold_Prop; simpl;
        try (destruct n as [|n]; [easy|])
    | |- match ?n with
         | O => True
         | S n' => wp _ _ _ _ _ _ n'
         end => destruct n as [|n]; [easy|step lemma]
    end.

  Lemma test_inv :
    NodeInv (fun v m => v = 10%Z) test 3
      ⌞ one ↦ᵣ 1 ∧ ten ↦ᵣ 10 ∧ ∃ v, x ↦ᵣ v ∧ ⌜v <= 10⌝%Z ⌟.
  Proof.
    apply löb.
    intros ρ m n IH (Hone & Hten & v & Hres & Hv).
    step wp_op.
    step wp_cond.
    destruct (10 - v =? 0)%Z eqn:He.
    - step wp_ret. repeat split. simpl_reg.
    - step wp_op. eapply safe_mono; [|apply IH].
      + lia.
      + simpl_reg. eexists. repeat split.
        lia.
  Qed.

  Lemma test_correct :
    hoare P (fun args m => True) test (fun v m => v = 10%Z).
  Proof.
    apply hoare_from_wp.
    intros args ρ m n _.
    step wp_op.
    step wp_op.
    step wp_op.
    apply test_inv. repeat (simpl_reg; unfold_Prop).
    eexists. repeat split. lia.
  Qed.

End Play.
