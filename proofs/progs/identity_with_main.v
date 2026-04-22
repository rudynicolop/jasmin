From Jasmin Require Export oracles.

Section prog.
  Context {pd: PointerData} `{asmop:asmOp}.

  (** Extraction oracles. *)
  Context (orc : oracles).

  Section identity.

    (** ** Identity function for integers. *)

    (** Variables. *)
    Definition tempx : var_i :=
      mk_var_i (Var aint (orc.(to_ident) "x" (Reg (Normal, Direct)) aint)).
    Definition tempr : var_i :=
      mk_var_i (Var aint (orc.(to_ident) "r" (Reg (Normal, Direct)) aint)).

  Definition identity_body : cmd :=
    [:: MkI dummy_instr_info
       (Cassgn (Lvar tempr) AT_keep aint (mk_lvar tempx))].

  Definition identity_def : _fundef unit :=
    {| f_info := orc.(fun_info_dummy)
    (* Ignore contracts. *)
    ; f_contract := None
    ; f_tyin := [:: aint]
    ; f_params := [:: tempx]
    ; f_body := identity_body
    ; f_tyout := [:: aint]
    ; f_res := [:: tempr]
    ; f_extra := tt
    |}.

  Definition identity_decl : _fun_decl unit :=
    (orc.(to_funname) "identity", identity_def).
  End identity.

  Section main.
    (** ** Main. *)

    (** Variables. *)
    Definition tempy : var_i :=
      mk_var_i (Var aint (orc.(to_ident) "y" (Reg (Normal, Direct)) aint)).
    Definition tempz : var_i :=
      mk_var_i (Var aint (orc.(to_ident) "z" (Reg (Normal, Direct)) aint)).

    (** TODO: on OCaml side, when we try to compile this,
        we get the error:
        "internal compilation error in function main:
         make reference arguments: unknown function"
     *)
    Definition main_body : cmd :=
      map (MkI dummy_instr_info)
        [::
         (** Call identity with [0%Z]. *)
         Ccall [:: Lvar tempy] (orc.(to_funname) "identity") [:: Pconst 0%Z];
         (** Assign to return var. *)
         Cassgn (Lvar tempz) AT_keep aint (mk_lvar tempy)
        ].

    Definition main_def : _fundef unit :=
      {| f_info := orc.(fun_info_dummy)
      (* Ignore contracts. *)
      ; f_contract := None
      (* No arguments. *)
      ; f_tyin := [::]
      ; f_params := [::]
      ; f_body := main_body
      (* Returns result of identity. *)
      ; f_tyout := [:: aint]
      ; f_res := [:: tempz]
      ; f_extra := tt
      |}.

    Definition main_decl : _fun_decl unit :=
      (orc.(to_funname) "main", main_def).
  End main.

  Definition call_identity_prog : _uprog :=
    {| p_funcs := [:: main_decl ; identity_decl ];
      (* No globals *)
      p_globs := [::];
      p_extra := tt;
    |}.
End prog.
