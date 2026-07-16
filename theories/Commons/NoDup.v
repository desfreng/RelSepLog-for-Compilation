From RSL Require Import Prelude.

Section NoDupProof.
  Context `{dec : EqDecision A}.

  Global Instance list_elem_of_dec : RelDecision (∈@{list A}).
  Proof using Type*.
   refine (
    fix go x l :=
    match l return Decision (x ∈ l) with
    | [] => right _
    | y :: l => cast_if_or (decide (x = y)) (go x l)
    end); clear go dec; subst; try (by constructor); abstract by inv 1.
  Defined.

  Fixpoint is_no_dup (l: list A) : bool :=
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

  Lemma no_dup_dec : ∀ l : list A, Decision (NoDup l).
  Proof using dec.
    intros l. destruct (is_no_dup l) eqn:H.
    - left. now apply is_no_dup_sound.
    - right. intro HD.
      apply is_no_dup_sound in HD.
      congruence.
  Qed.
End NoDupProof.
