From RSL Require Import Prelude.

From Coinduction Require Import all.

From RSL.Simulations Require Export LockStep Implicit.

Section PROOF.
  Context {Λt Λs: lang}.
  Context (Et: genv Λt) (Es: genv Λs).
  Context (ϕ: post Λt Λs).

  Lemma lsim_implies_isim t s :
    lsim Et Es ϕ t s ->
    isim Et Es ϕ t s.
  Proof using Type.
    revert t s.
    unfold isim.
    coinduction R CIH.
    intros t s Hsim.
    apply lsim_unroll in Hsim.
    induction Hsim as [ t s Hfinal
                      | t s s' Hs Hstuck
                      | t s Hprogress Hboth ].
    - (* Both Final *)
      now constructor.
    - (* Source Stuck *)
      induction Hs as [ s | s s' s'' Hs Hrtc IH ].
      + now constructor.
      + eapply ISourceSteps.
        * done.
        * by apply IH.
    - apply IBothSteps. { done. }
      intros t' Ht.
      specialize (Hboth _ Ht) as (s' & Hs & Hsim).
      exists s'. split.
      + done.
      + by apply CIH.
  Qed.

End PROOF.
