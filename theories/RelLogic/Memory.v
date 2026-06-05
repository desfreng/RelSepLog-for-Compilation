From RSL Require Import Prelude.

From stdpp Require Import gmap.
From RSL Require Import Commons.RegisterBank.

Definition rbank : Type := regbank * regbank.

Class RLogicTargetAssert (R V : Type) :=
  rbank_assert_t : rbank -> R -> V -> Prop.

Instance rbank_assert_t_single : RLogicTargetAssert _ _ :=
  fun '(ρₜ, _) key val => get_reg ρₜ key = val.

Instance rbank_assert_t_list : RLogicTargetAssert (list _) (list _) :=
  fun '(ρₜ, _) keys vals => map (get_reg ρₜ) keys = vals.

Definition rbank_update_t '((ρₜ, ρₛ) : rbank) key f : rbank :=
  (update_reg ρₜ key f, ρₛ).

Definition rbank_set_t Γ key val : rbank :=
  rbank_update_t Γ key (fun _ => val).

Class RLogicSourceAssert (R V : Type) :=
  rbank_assert_s : rbank -> R -> V -> Prop.

Instance rbank_assert_s_single : RLogicSourceAssert _ _ :=
  fun '(_, ρₛ) key val => get_reg ρₛ key = val.

Instance rbank_assert_s_list : RLogicSourceAssert (list _) (list _) :=
  fun '(_, ρₛ) keys vals => map (get_reg ρₛ) keys = vals.

Definition rbank_update_s '((ρₜ, ρₛ) : rbank) key f : rbank :=
  (ρₜ, update_reg ρₛ key f).

Definition rbank_set_s Γ key val : rbank :=
  rbank_update_s Γ key (fun _ => val).

Notation "Γ @ r '⇒ₜ' v" :=
  (rbank_assert_t Γ r%nat v%Z)
    (at level 60, no associativity).

Notation "Γ @ r '⇒ₛ' v" :=
  (rbank_assert_s Γ r%nat v%Z)
    (at level 60, no associativity).

Notation "'⟦' r '⇐ₜ' v '⟧' Γ" :=
  (rbank_set_t Γ r%nat v%Z)
    (at level 20, Γ at level 20, right associativity).

Notation "'⟦' r '⇐ₛ' v '⟧' Γ" :=
  (rbank_set_s Γ r%nat v%Z)
    (at level 20, Γ at level 20, right associativity).

Notation "'⟦' r '⇐ₜ' 'λ' v '.' f '⟧' Γ" :=
  (rbank_update_t Γ r%nat (fun v => f))
    (at level 20, v binder, Γ at level 20, right associativity).

Notation "'⟦' r '⇐ₛ' 'λ' v '.' f '⟧' Γ" :=
  (rbank_update_s Γ r%nat (fun v => f))
    (at level 20, v binder, Γ at level 20, right associativity).

Notation "'⟦' r '⇐ₜ' 'fun' v '.' f '⟧' Γ" :=
  (rbank_update_t Γ r%nat (fun v => f))
    (at level 20, v binder, Γ at level 20, right associativity).

Notation "'⟦' r '⇐ₛ' 'fun' v '.' f '⟧' Γ" :=
  (rbank_update_s Γ r%nat (fun v => f))
    (at level 20, v binder, Γ at level 20, right associativity).

Notation "'⟦' rt '⇐ₜ' vt ',' rs '⇐ₛ' vs '⟧' Γ" :=
  (rbank_update_t (rbank_update_s Γ rs%nat vs%Z) rt%nat vt%Z)
    (at level 20, Γ at level 20, right associativity).

Notation "'⟦' rs '⇐ₛ' vs ',' rt '⇐ₜ' vt '⟧' Γ" :=
  (rbank_update_t (rbank_update_s Γ rs%nat vs%Z) rt%nat vt%Z)
    (at level 20, Γ at level 20, right associativity).
