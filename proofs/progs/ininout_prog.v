From Jasmin Require Export oracles.

Section prog.
  Context {pd: PointerData} `{asmop:asmOp}.

  (** Extraction oracles. *)
  Context (orc : oracles).

  (** ** Main. *)

  (** Variables. *)
  Definition tempz : var_i :=
    mk_var_i (Var aint (orc.(to_ident) "z" (Reg (Normal, Direct)) aint)).

  Definition main_body : cmd :=
    map (MkI dummy_instr_info)
      [::
         (** Assign [0] to return var. *)
         Cassgn (Lvar tempz) AT_keep aint 0%Z
      ].

  (** Output [0]. *)
  Definition main_def : _fundef unit :=
    {| f_info := orc.(to_fun_info) 1
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
