From RSL Require Import Prelude.

From RSL.RTL Require Export RTL Semantics Notations.
From RSL.Logic Require Export Logic.

Import RTLNotations.

Definition hoare {J I} Pt Ps C Pre ft j i fs Post : rProp :=
  □ (∀ valt vals,
       Pre valt vals -∗
       (* (∀ vt vs, Post vt vs -∗ Ψ vt vs) -∗ *)
       @sim_lfp rtl_lang rtl_lang J I Pt Ps C
         ([], CallState ft valt) j i ([], CallState fs vals) Post
    )%I.

Notation
  "'[' Pt ',' Ps ',' C ']' '{{' P '}}' ft '<{' j ',' i '}=' fs '{{' Q '}}'" :=
  (hoare Pt Ps C P%I ft j i fs Q%I)
    (at level 0, ft at level 0, fs at level 0, no associativity).

Section HoareRules.
  Context {J I: WfRel}.
  Context {Pt Ps : prog rtl_lang}.

  Implicit Type C : Chain (fsim_lfp J I Pt Ps).
  Context {C}.

  Context {ft : rtl_function} {j: J} {i: I} {fs : rtl_function}.

  (* Lemma frame F P Q: *)
  (*   [Pt, Ps, C] {{ P }} ft <{j, i}= fs {{ Q }} -∗ *)
  (*   [Pt, Ps, C] {{ fun valt vals => P valt vals ∗ F }} ft <{j, i}= fs {{ fun vt vs => Q vt vs ∗ F }}. *)
  (* Proof using Type. *)
  (*   unfold hoare. unseal. *)
  (*   intros ? ? [-> ->] mt ms _ _ [[-> ->] Hsim]. smap. *)
  (*   split. { by split. } *)
  (*   intros valt vals. *)
  (*   intros a b _ _ Hpre. smap. *)
  (*   destruct Hpre as (mtP & msP & mtF & msF & Ht & Hs & <- & <- & HP & HF). simpl. *)
  (*   apply Hsim in HP; try apply map_disjoint_empty_r. clear Hsim. *)
  (*   revert mtP msP mtF msF HF Ht Hs HP. simpl. *)
  (*   apply tower. *)
  (*   { admit. } *)
  (*   clear C. intros C CIH. *)
  (*   intros mtP msP mtF msF HF Ht Hs Hsim. *)
  (*   induction Hsim. *)
  (*   - apply FRelated.  *)
  (*   simpl. *)
  (*   iIntros "#H !>" (valt vals Ψ) "[Hpre Hf] Hpost". *)
  (*   iApply ("H" with "Hpre"). *)
  (*   iIntros (vt vs) "Hq". iApply "Hpost". *)
  (*   by iFrame. *)
  (* Qed. *)

  (* Lemma consequence P P' Q Q': *)
  (*   □ (∀ valt vals, P valt vals -∗ P' valt vals) -∗ *)
  (*   □ (∀ vt vs, Q' vt vs -∗ Q vt vs) -∗ *)
  (*   [Pt, Ps, C] {{ P' }} ft <{j, i}= fs {{ Q' }} -∗ *)
  (*   [Pt, Ps, C] {{ P }} ft <{j, i}= fs {{ Q }}. *)
  (* Proof using Type. *)
  (*   iIntros "#HP #HQ #H !>" (valt vals Ψ) "Hpre Hpost". *)
  (*   iApply ("H" with "[Hpre] [Hpost]"). *)
  (*   - by iApply "HP". *)
  (*   - iIntros (vt vs) "HQ'". iApply "Hpost". by iApply "HQ". *)
  (* Qed. *)
End HoareRules.
