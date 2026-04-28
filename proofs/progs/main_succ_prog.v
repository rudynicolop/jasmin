From Jasmin Require Export oracles.

Section prog.
  Context
    {pd: PointerData} `{asmop:asmOp}

    (** Extraction oracles *)
    (orc : oracles).

  (** ** Main. *)

  Notation aword32 := (aword U32).

  (* NOTE: have [main_def] "generate" and pass in variables *)
  Definition main_body (tempy tempz : var_i) : cmd :=
    map (MkI dummy_instr_info)
      [::
         (** Perform succession. *)
         Cassgn (Lvar tempz) AT_none aword32
         (Papp2 (Oadd (Op_w U32)) (Papp1 (Oword_of_int U32) 1%Z) (mk_lvar tempy))
      ].

  (** Return the successor of the input value. *)
  Definition main_def : _fundef unit :=
    (* NOTE: make sure variables are only "generated once": *)
    let tempy : var_i := mk_var_i (Var aword32 (orc.(to_ident) "y" (Reg (Normal, Direct)) aword32)) in
    let tempz : var_i := mk_var_i (Var aword32 (orc.(to_ident) "z" (Reg (Normal, Direct)) aword32)) in
    {| f_info := orc.(to_fun_info) 1
    (* Ignore contracts. *)
    ; f_contract := None
    (* No arguments. *)
    ; f_tyin := [:: aword32]
    ; f_params := [:: tempy]
    ; f_body := main_body tempy tempz
    (* Returns result of identity. *)
    ; f_tyout := [:: aword32]
    ; f_res := [:: tempz]
    ; f_extra := tt
    |}.

  Definition main_decl : _fun_decl unit :=
    (orc.(to_funname) "main", main_def).

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
