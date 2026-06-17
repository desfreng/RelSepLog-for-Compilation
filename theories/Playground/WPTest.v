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

  Definition NodeInv f pc Q (NI : regbank -> logic) : Prop :=
    ⌜⌝ ⊩ ∀ ρ, NI ρ -> wp P ρ f pc Q.

  Definition test : function :=
    {|
      fn_name := "test"%string;
      fn_regs := [];
      fn_entrypoint := 0;
      fn_code := <<{{
            0: x := #0 -> 1;
            1: one := #1 -> 2;
            2: ten := #10 -> 3;
            3: diff := ten - x -> 4;
            4: if diff then goto 6 else goto 5;
            5: x := x + one -> 3;
            6: ret x;
        }}>>;
      fn_regs_no_dup := eq_refl;
    |}.


  Ltac step_acc Hpc :=
    lazymatch type of Hpc with
    | _ @ _ is Iop _ _ _ _ =>
        eapply wp_op; [exact Hpc | simregs | reflexivity | ]

    | _ @ _ is Icond _ _ _ =>
        eapply wp_cond; [exact Hpc | simregs | reflexivity | ]

    | _ @ _ is Ireturn _ =>
        eapply wp_ret; [exact Hpc | simregs | ]

    | _ @ _ is ?i  => idtac "Fail with " i; fail
    end.

  Ltac step :=
    lazymatch goal with
    | |- wp _ _ ?f ?pc _ ?n _ =>
        let H := fresh "Hpc" in
        eassert (H: f@pc is _) by reflexivity;
        step_acc H;
        clear H;
        destruct n as [|n]; [easy| simpl]; unfold_Prop
    end.

  Lemma test_inv :
    NodeInv test 3 (fun v m => v = 10%Z)
      ⦇fun ρ =>
         ∃ v,
         ⌜ρ @ one ⇒ 1⌝ ∧
         ⌜ρ @ ten ⇒ 10⌝ ∧
         ⌜ρ @ x ⇒ v⌝ ∧
         ⌜v <= 10⌝%Z
      ⦈.
  Proof using Type.
    unfold NodeInv.
    apply löb.
    intros n m IH ρ (v & Hone & Hten & Hres & Hv); unfold_Prop.
    step.
    step.
    destruct (10 - v =? 0)%Z eqn:He.
    - step. lia.
    - step.
      eapply safe_mono; [|apply IH].
      + lia.
      + easy.
      + exists (v + 1)%Z. repeat split.
        * simregs.
        * simregs.
        * simregs.
        * lia.
  Qed.

  Lemma test_correct :
    hoare P (fun args m => True) test (fun v m => v = 10%Z).
  Proof using Type.
    apply hoare_from_wp.
    intros ρ args H n m _.
    step.
    step.
    step.
    apply test_inv.
    - easy.
    - unfold_Prop.
      exists 0%Z. repeat split.
      + simregs.
      + simregs.
      + simregs.
      + lia.
  Qed.

End Play.
