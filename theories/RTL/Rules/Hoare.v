From RSL Require Import Prelude.

From RSL.RTL Require Export RTL Semantics Notations.
From RSL.Logic Require Export Logic.

Import RTLNotations.

Definition hoare {J I} Pt Ps C Pre ft j i fs Post : rProp :=
  □ (∀ valt vals Ψ,
       Pre valt vals -∗
       (∀ vt vs, Post vt vs -∗ Ψ vt vs) -∗
       @sim_lfp rtl_lang rtl_lang J I Pt Ps C
         ([], CallState ft valt) j i ([], CallState fs vals) Ψ
    )%I.

Notation
  "'[' Pt ',' Ps ',' C ']' '{{' P '}}' ft '<{' j ',' i '}=' fs '{{' Q '}}'" :=
  (hoare Pt Ps C P%I ft j i fs Q%I)
    (at level 0, ft at level 0, fs at level 0, no associativity).

Section HoareRules.
  Context {J I: WfRel}.
  Context {Pt Ps : prog rtl_lang}.
  Context {C : Chain (fsim_lfp J I Pt Ps)}.
  Context {ft : rtl_function} {j: J} {i: I} {fs : rtl_function}.

  Lemma frame F P Q:
    [Pt, Ps, C] {{ P }} ft <{j, i}= fs {{ Q }} -∗
    [Pt, Ps, C] {{ fun valt vals => P valt vals ∗ F }} ft <{j, i}= fs {{ fun vt vs => Q vt vs ∗ F }}.
  Proof using Type.
    iIntros "#H !>" (valt vals Ψ) "[Hpre Hf] Hpost".
    iApply ("H" with "Hpre").
    iIntros (vt vs) "Hq". iApply "Hpost".
    by iFrame.
  Qed.

  Lemma consequence P P' Q Q':
    □ (∀ valt vals, P valt vals -∗ P' valt vals) -∗
    □ (∀ vt vs, Q' vt vs -∗ Q vt vs) -∗
    [Pt, Ps, C] {{ P' }} ft <{j, i}= fs {{ Q' }} -∗
    [Pt, Ps, C] {{ P }} ft <{j, i}= fs {{ Q }}.
  Proof using Type.
    iIntros "#HP #HQ #H !>" (valt vals Ψ) "Hpre Hpost".
    iApply ("H" with "[Hpre] [Hpost]").
    - by iApply "HP".
    - iIntros (vt vs) "HQ'". iApply "Hpost". by iApply "HQ".
  Qed.

  Local Definition hoare_ind_inv Inv
    (st: pstate rtl_lang) (j': J) (i': I) (ss : pstate rtl_lang)
    (ϕ: val -> val -> rProp) : rProp :=
    ∃ ft fs valt vals P Ψ,
      ⌜st = ([], CallState ft valt) ∧
       ss = ([], CallState fs vals)⌟ ∗
      ⌜Inv P ft j' i' fs Ψ⌟ ∗
      P valt vals ∗
      (∀ vt vs, Ψ vt vs -∗ ϕ vt vs).

  Lemma hoare_ind Inv P Q:
    □ (∀ C P ft j i fs Q valt vals Ψ,
         □ (∀ P ft j' i' fs Q,
              ⌜j ⊏ j'⌟ -∗
              ⌜i ⊏ i'⌟ -∗
              ⌜Inv P ft j i fs Q⌟ -∗
              [Pt, Ps, C] {{ P }} ft <{j', i'}= fs {{ Q }}
         ) -∗
         ⌜Inv P ft j i fs Q⌟ -∗
         P valt vals -∗
         (∀ vt vs, Q vt vs -∗ Ψ vt vs) -∗
         [Pt, Ps, C] ([], CallState ft valt) <{j, i}= ([], CallState fs vals) {{ Ψ }}
    ) -∗
    ⌜Inv P ft j i fs Q⌟ -∗
    [Pt, Ps, C] {{ P }} ft <{j, i}= fs {{ Q }}.
  Proof using Type.
    iIntros "#RIH %HInv !>".
    iIntros (valt vals Ψ) "HPre HPost".
    iApply (coind (hoare_ind_inv Inv)).
    - clear.
      iIntros "!>" (C st j i ss Ψ) "#CIH".
      iIntros "(%ft & %fs & %valt & %vals & %P & %Q & %H & Hinv & Hpre & Hpost)".
      destruct H as (-> & ->).
      iApply ("RIH" with "[] Hinv Hpre Hpost").
      clear.
      iIntros "!>" (P ft j' i' fs Q Hj Hi Hinv).
      iIntros "!>" (valt vals Ψ) "HPre HPost".
      iApply ("CIH").
      + by iPureIntro.
      + by iPureIntro.
      + iExists ft, fs, valt, vals, P, Q. iFrame. iPureIntro.
        by split_and!.
    - iExists ft, fs, valt, vals, P, Q. iFrame. iPureIntro.
      by split_and!.
  Qed.
End HoareRules.
