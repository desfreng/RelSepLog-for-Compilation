From RSL Require Import Prelude.

Section NoDupProof.
  Context `{dec : EqDecision A}.
  Implicit Types (l: list A).

  Fixpoint is_no_dup l : bool :=
    match l with
    | [] => true
    | hd :: tl =>
        if decide_rel (∈) hd tl
        then false
        else is_no_dup tl
    end.

  Lemma is_no_dup_sound:
    ∀ l, is_no_dup l = true <-> NoDup l.
  Proof using Type.
    intros l. induction l as [ | hd tl IH ].
    - split; constructor.
    - simpl; destruct (decide_rel elem_of hd tl) as [He | Hne].
      + split; intro H.
        * discriminate H.
        * exfalso. inv H as [ | ? ? Hne ]. now apply Hne.
      + split; intro H.
        * constructor; auto. now apply IH.
        * apply IH. now inv H.
  Qed.

  Lemma no_dup_dec : ∀ l, Decision (NoDup l).
  Proof using dec.
    intros l. destruct (is_no_dup l) eqn:H.
    - left. now apply is_no_dup_sound.
    - right. intro HD.
      apply is_no_dup_sound in HD.
      congruence.
  Qed.
End NoDupProof.
