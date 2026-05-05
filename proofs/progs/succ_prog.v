From Jasmin Require Export oracles.

Section prog.
  Context
    {pd: PointerData} `{asmop:asmOp}

    (** Extraction oracles *)
    (orc : oracles).

  (** ** Successor. *)

  Notation aword32 := (aword U32).

  (* NOTE: have [succ_def] "generate" and pass in variables *)
  Definition succ_body (tempy tempz : var_i) : cmd :=
    map (MkI dummy_instr_info)
      [::
         (** Perform succession. *)
         Cassgn (Lvar tempz) AT_none aword32
         (Papp2 (Oadd (Op_w U32)) (Papp1 (Oword_of_int U32) 1%Z) (mk_lvar tempy))
      ].

  (** Return the successor of the input value. *)
  Definition succ_def : _fundef unit :=
    (* NOTE: make sure variables are only "generated once": *)
    let tempy : var_i := mk_var_i (Var aword32 (orc.(to_ident) "y" (Reg (Normal, Direct)) aword32)) in
    let tempz : var_i := mk_var_i (Var aword32 (orc.(to_ident) "z" (Reg (Normal, Direct)) aword32)) in
    {| f_info := orc.(to_fun_info) 1
    (* Ignore contracts. *)
    ; f_contract := None
    (* No arguments. *)
    ; f_tyin := [:: aword32]
    ; f_params := [:: tempy]
    ; f_body := succ_body tempy tempz
    (* Returns result of identity. *)
    ; f_tyout := [:: aword32]
    ; f_res := [:: tempz]
    ; f_extra := tt
    |}.

  Definition succ_decl : _fun_decl unit :=
    (orc.(to_funname) "successor", succ_def).

  Definition prog : _uprog :=
    {| p_funcs := [:: succ_decl ];
      (* No globals *)
      p_globs := [::];
      p_extra := tt;
    |}.
End prog.

Require Import QuickChick.QuickChick.

(* Fail QCDerive Show for _uprog. *)
(* Error: Anomaly "Uncaught exception Failure("destIndRef")." Please report at http://rocq-prover.org/bugs/. *)

Fail QCDerive Show for pexpr.
QCDerive Show for wsize.
QCDerive Show for positive.
QCDerive Show for atype.
Axiom show_ident : Show Ident.ident.
Existing Instance show_ident.
Instance show_var : Show var := {|
                                 show :=
fun x : var =>
 match x with
 | {| vtype := p0; vname := p1 |} =>
     ("Var " ++ smart_paren (show p0) ++ " " ++ smart_paren (show p1))%string
 end |}.
Axiom show_var_info : Show var_info.
Existing Instance show_var_info.
Fail QCDerive Show for var_i.
QCDerive Show for gvar.
QCDerive Show for aligned.
QCDerive Show for arr_access.
QCDerive Show for wsize.
QCDerive Show for gvar.
QCDerive Show for arr_access.
QCDerive Show for wsize.
QCDerive Show for positive.
QCDerive Show for gvar.
QCDerive Show for aligned.
QCDerive Show for wsize.
QCDerive Show for sop1.
QCDerive Show for sop2.
QCDerive Show for opN.
QCDerive Show for pexprs.
QCDerive Show for atype.
