From Stdlib Require Import Utf8.

From RSL Require Import RTL.
From RSL Require Import Semantics.

Definition postcondition : Type := val -> memory -> Prop.
Definition sProp : Type := nat -> regmap * memory -> Prop.

Declare Scope sProp_scope.
Delimit Scope sProp_scope with sProp.
Bind Scope sProp_scope with sProp.

Definition sProp_and (P Q : sProp) : sProp :=
  fun n p => P n p ∧ Q n p.

Notation "P ∧ Q" :=
  (sProp_and P Q) : sProp_scope.

Definition sProp_or (P Q : sProp) : sProp :=
  fun n p => P n p ∨ Q n p.

Notation "P ∨ Q" :=
  (sProp_or P Q) : sProp_scope.

Definition sProp_impl (P Q : sProp) : sProp :=
  fun n p => P n p -> Q n p.

Notation "P -> Q" :=
  (sProp_impl P Q) : sProp_scope.

Definition sProp_not (P : sProp) : sProp :=
  fun n p => ~ P n p.

Notation "~ P" :=
  (sProp_not P) : sProp_scope.

Definition sProp_exists {A : Type} (f : A -> sProp) : sProp :=
  fun n p => ∃ x : A, f x n p.

Notation "'∃' x .. y , p" :=
  (sProp_exists (fun x => .. (sProp_exists (fun y => p)) ..)) : sProp_scope.

Definition sProp_forall {A : Type} (f : A -> sProp) : sProp :=
  fun n p => ∀ x : A, f x n p.

Notation "'∀' x .. y , p" :=
  (sProp_forall (fun x => .. (sProp_forall (fun y => p)) ..)) : sProp_scope.

Definition sProp_pure (P : Prop) : sProp :=
  fun _ _ => P.

Notation "⌜ P ⌝" :=
  (sProp_pure P)
    (at level 0, format "⌜ P ⌝") : sProp_scope.

Definition sProp_later (P : sProp) : sProp :=
  fun n =>
    match n with
    | O => fun _ => True
    | S n => fun p => P n p
    end.

Notation "▷ P" :=
  (sProp_later P)
    (at level 20, right associativity, format "▷ P") : sProp_scope.

Definition sProp_always (P : sProp) : sProp :=
  fun _ p => ∀ n, P n p.

Notation "□ P" :=
  (sProp_always P)
    (at level 20, right associativity, format "□ P") : sProp_scope.

Definition sProp_entails (P Q : sProp) : Prop :=
  ∀ n p, P n p -> Q n p.

Notation "P ⊢ Q" :=
  (sProp_entails P%sProp Q%sProp)
    (at level 99, right associativity).

Definition sProp_ask (F : regmap -> memory -> sProp) : sProp :=
  fun n '(ρ, m) => F ρ m n (ρ, m).

Notation "'λₛ' ρ m , P" :=
  (sProp_ask (fun ρ m => P))
    (at level 200,
        ρ name,
        m name,
        right associativity,
        format "'λₛ' ρ  m  ,  P") : sProp_scope.

Definition sProp_put (ρ : regmap) (m : memory) (P : sProp) : sProp :=
  fun n _ => P n (ρ, m).

Notation "P '⟨' ρ ',' m '⟩'" :=
  (sProp_put ρ m P)
    (at level 11,
        left associativity,
        format "P  '⟨' ρ ','  m '⟩'") : sProp_scope.

Create HintDb custom_sProp discriminated.

Hint Unfold
  sProp_and
  sProp_or
  sProp_impl
  sProp_not
  sProp_exists
  sProp_forall
  sProp_pure
  sProp_later
  sProp_always
  sProp_entails
  sProp_ask
  sProp_put
: custom_sProp.

Ltac unfold_sProp :=
  autounfold with custom_sProp in *;
  cbv beta in *;
  simpl in *.

Definition mono (P : sProp) : Prop :=
  ∀ n p, P (S n) p -> P n p.

Lemma later_intro S :
  mono S -> S ⊢ ▷ S.
Proof.
  intros Hmono.
  unfold_sProp.
  intros [|n] p Hs.
  - exact I.
  - apply Hmono. exact Hs.
Qed.

Lemma löb S P :
  mono S ->
  (S ∧ ▷ P ⊢ P) -> S ⊢ P.
Proof.
  intros Hmono H n [ρ m] Hs.
  induction n as [|n IHn].
  - apply H. split.
    + assumption.
    + easy.
  - apply H. split.
    + assumption.
    + apply IHn.
      apply Hmono. assumption.
Qed.
