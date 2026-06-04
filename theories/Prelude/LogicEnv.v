(** ** Custom context structure *)

Structure LEnv := {
    (** Environment type with coercion. *)
    E :> Type;
    (** Keys *)
    Key : Type;
    (** Values *)
    Val : Type;
    (** Get handler  *)
    get_data : E -> Key -> option Val;
    (** Update handler *)
    update_data : E -> Key -> (Val -> Val) -> option E;
}.

Arguments get_data {_} _ _.
Arguments update_data {_} _ _ _.
