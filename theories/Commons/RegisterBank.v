From RSL Require Import Prelude.

From stdpp Require Import gmap.

Definition reg := nat.

(* [regmap] is a mapping from registers to a value *)
Definition regbank : Type := gmap reg val.

Definition get_reg (ρ: regbank) (r: reg) : val :=
  match ρ !! r with
  | Some v => v
  | None => 0%Z (* Default val *)
  end.

Definition update_reg (ρ: regbank) (r: reg) (f: val -> val) : regbank :=
  let old := get_reg ρ r in <[r := f old]>ρ.

Canonical Structure regbank_ctx : LEnv :=
  {|
    get_data ρ r := Some $ get_reg ρ r;
    update_data ρ r f := Some $ update_reg ρ r f;
  |}.

Definition set_reg (r: reg) (v: val) (ρ: regbank) : regbank :=
  update_reg ρ r (fun _ => v).

(* Fixpoint init_regs (vl: list val) (rl: list reg) : regbank := *)
(*   match rl, vl with *)
(*   | r :: rs, v :: vs => <[r := v]>(init_regs vs rs) *)
(*   | _, _ => ∅ *)
(*   end. *)

(* Lemma get_regs_insert : ∀ regs r v ρ, *)
(*   r ∉ regs -> *)
(*   Forall (fun reg => get_reg (<[r := v]> ρ) reg = get_reg ρ reg) regs. *)
(* Proof using Type. *)
(*   intros regs r v ρ. *)
(*   intros Hnotin. *)
(*   induction regs as [ | r' regs IH]; constructor. *)
(*   - unfold get_reg. rewrite (lookup_insert_ne ρ). *)
(*     + reflexivity. *)
(*     + intros ->. apply Hnotin. left. *)
(*   - apply IH. intros Hin. apply Hnotin. now right. *)
(* Qed. *)

(* Lemma get_regs_init_regs : ∀ regs args, *)
(*   NoDup regs -> *)
(*   length args = length regs -> *)
(*   get_regs (init_regs args regs) regs = args. *)
(* Proof using Type. *)
(*   intros regs args Hnodup. *)
(*   revert args. *)
(*   induction Hnodup as [|r regs Hnotin Hnodup IH]; intros args Hlen. *)
(*   - destruct args; [reflexivity | discriminate Hlen]. *)
(*   - destruct args as [|v args]; [discriminate Hlen |]. *)
(*     simpl in Hlen. injection Hlen as Hlen'. *)
(*     simpl. f_equal. *)
(*     + unfold get_reg. now rewrite (lookup_insert_eq (init_regs args regs)). *)
(*     + rewrite get_regs_insert by exact Hnotin. *)
(*       apply IH. exact Hlen'. *)
(* Qed. *)
