From RSL Require Import Prelude.

Section CommonsDef.
  Context {Λₜ Λₛ: lang}.
  Context (Φ: value Λₜ -> value Λₛ -> Prop).

  Definition is_final (t: state Λₜ) (s: state Λₛ) : Prop :=
    ∃ vₜ vₛ, is_final t = Some vₜ ∧ is_final s = Some vₛ ∧ Φ vₜ vₛ.

End CommonsDef.
