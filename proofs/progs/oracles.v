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

    (** Generate function info
        Yes, [FunInfo.witness] is completely useless, since:
        - extraction hides the type [t] of extracted [FunInfo.t] under a
          module signature, OCaml expects parameter [f_info] to have
          type [fun_info = FInfo.t], not [fun_info = FunInfo.t]... yikes...
        - A general dummy value does not work, since the [fun_info] needs to
          encode information specific to the function.
          Specifically, the number of annotations in the return info needs
          to equal the length of return variables.
          TODO: is this correct?
     *)
    to_fun_info : nat -> fun_info;

    (** Get variable identifiers.
        NOTE: The OCaml type for identifiers [CoreIdent.Cident.t] also
        requires:
        - redundant type information.
        - the "kind" of variable (register, stack, constant, etc) *)
    to_ident : string -> v_kind -> atype -> Ident.ident;
  }.
