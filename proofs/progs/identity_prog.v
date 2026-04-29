From Jasmin Require Export oracles.

Section prog.
  Context
    {pd: PointerData} `{asmop:asmOp}

    (** Extraction oracles *)
    (orc : oracles).

  (** ** Identity. *)

  Notation aword32 := (aword U32).

  (* NOTE: have [identity_def] "generate" and pass in variables *)
  Definition identity_body (tempy tempz : var_i) : cmd :=
    map (MkI dummy_instr_info)
      [::
         (** Assign the same number. *)
         Cassgn (Lvar tempz) AT_none aword32 (mk_lvar tempy)
      ].

  (** Return the input value. *)
  Definition identity_def : _fundef unit :=
    (* NOTE: make sure variables are only "generated once": *)
    let tempy : var_i := mk_var_i (Var aword32 (orc.(to_ident) "y" (Reg (Normal, Direct)) aword32)) in
    let tempz : var_i := mk_var_i (Var aword32 (orc.(to_ident) "z" (Reg (Normal, Direct)) aword32)) in
    {| (* Pass [1] so the number of annotations for
          "return" matches the number of result variables. *)
      f_info := orc.(to_fun_info) 1
    (* Ignore contracts. *)
    ; f_contract := None
    (* No arguments. *)
    ; f_tyin := [:: aword32]
    ; f_params := [:: tempy]
    ; f_body := identity_body tempy tempz
    (* Returns result of identity. *)
    ; f_tyout := [:: aword32]
    ; f_res := [:: tempz]
    ; f_extra := tt
    |}.

  Definition identity_decl : _fun_decl unit :=
    (orc.(to_funname) "identity", identity_def).

  Definition prog : _uprog :=
    {| p_funcs := [:: identity_decl ];
      (* No globals *)
      p_globs := [::];
      p_extra := tt;
    |}.
End prog.
