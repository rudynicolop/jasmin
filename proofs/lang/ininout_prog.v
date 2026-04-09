From Jasmin Require Export hoare_logic.
From Jasmin Require Import it_sems_core core_logics.
From Jasmin Require Import expr oseq psem_core.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import Stdlib.micromega.Lia.

Section prog.
  Context
    {pd: PointerData} `{asmop:asmOp}

    (** Get function name identifiers.
        NOTE: It is *CRITICAL* that we use [funname] here, no
        [FunName.t], which is hidden after extraction! *)
    (to_funname : string -> funname)

    (** Dummy function info
        Yes, [FunInfo.witness] is completely useless, since
        extraction hides the type [t] of extracted [FunInfo.t] under a
        module signature, OCaml expects parameter [f_info] to have
        type [fun_info = FInfo.t], not [fun_info = FunInfo.t]... yikes... *)
    (fun_info_dummy : fun_info)

    (** Get variable identifiers.
        NOTE: The OCaml type for identifiers [CoreIdent.Cident.t] also
        requires:
        - redundant type information.
        - the "kind" of variable (register, stack, constant, etc)
     *)
    (to_ident : string -> v_kind -> atype -> Ident.ident)
  .

  (** ** Main. *)

  (** Variables. *)
  Definition tempz : var_i :=
    mk_var_i (Var aint (to_ident "z" (Reg (Normal, Direct)) aint)).

  Definition main_body : cmd :=
    map (MkI dummy_instr_info)
      [::
         (** Assign [0] to return var. *)
         Cassgn (Lvar tempz) AT_keep aint 0%Z
      ].

  (** Output [0]. *)
  Definition main_def : _fundef unit :=
    {| f_info := fun_info_dummy
    (* Ignore contracts. *)
    ; f_contract := None
    (* No arguments. *)
    ; f_tyin := [:: ]
    ; f_params := [:: ]
    ; f_body := main_body
    (* Returns result of identity. *)
    ; f_tyout := [:: aint]
    ; f_res := [:: tempz]
    ; f_extra := tt
    |}.

  Definition main_decl : _fun_decl unit :=
    (to_funname "main", main_def).

  (**
     TODO: I get a fatal error when I try to compile this program in OCaml:
     [Fatal error: exception Invalid_argument("List.map2: list lengths differ")]
   *)
  Definition prog : _uprog :=
    {| p_funcs := [:: main_decl ];
      (* No globals *)
      p_globs := [::];
      p_extra := tt;
    |}.
End prog.
