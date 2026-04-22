From Jasmin Require Export expr.

(*** Oracles for Opaque Data *)

(** This file contains a record of oracles for generaring data hidden
    under module constraints in Rocq.
    These oracles are meant to be instantiated by a "bridge" function
    on the OCaml side after extraction. *)

Structure oracles := Oracles {
    (** Get function name identifiers.
        NOTE: It is *CRITICAL* that we use [funname] here, no
        [FunName.t], which is hidden after extraction! *)
    to_funname : string -> funname;

    (** Dummy function info
        Yes, [FunInfo.witness] is completely useless, since
        extraction hides the type [t] of extracted [FunInfo.t] under a
        module signature, OCaml expects parameter [f_info] to have
        type [fun_info = FInfo.t], not [fun_info = FunInfo.t]... yikes... *)
    fun_info_dummy : fun_info;

    (** Get variable identifiers.
        NOTE: The OCaml type for identifiers [CoreIdent.Cident.t] also
        requires:
        - redundant type information.
        - the "kind" of variable (register, stack, constant, etc) *)
    to_ident : string -> v_kind -> atype -> Ident.ident;
  }.
