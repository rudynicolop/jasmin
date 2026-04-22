From Jasmin Require Export oracles.

Section prog.
  Context {pd: PointerData} `{asmop:asmOp}.

  (** Extraction oracles *)
  Context (orc : oracles).

  Definition main_def : _fundef unit :=
    {| f_info := orc.(to_fun_info) 0
    (* Ignore contracts. *)
    ; f_contract := None
    (* No arguments. *)
    ; f_tyin := [::]
    ; f_params := [::]
    (* Empty body. *)
    ; f_body := [::]
    (* Returns nothing *)
    ; f_tyout := [::]
    ; f_res := [::]
    ; f_extra := tt
    |}.
 
  Definition main_decl : _fun_decl unit :=
    (orc.(to_funname) "main", main_def).

  Definition empty_prog : _uprog :=
    {|
      p_funcs := [:: main_decl];
      (* No globals *)
      p_globs := [::];
      p_extra := tt;

  |}.
End prog.
