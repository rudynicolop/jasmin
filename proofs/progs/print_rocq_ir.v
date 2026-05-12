From Jasmin Require Export global pseudo_operator sopn expr.
From Jasmin Require Export oracles.
Require Export mathcomp.ssreflect.seq.

(** NOTE: This should export [Show] for lists? *)
Require Import QuickChick.QuickChick.

(** [QCDerive] emits these warnings for non-recursive data types. *)
Local Set Warnings "-non-recursive".

(*** Print Rocq IR *)

(** A (not pretty/ugly) printer for the Rocq-level Jasmin IR. *)

(* Fail QCDerive Show for _uprog. *)
(* Error: Anomaly "Uncaught exception Failure("destIndRef")." Please report at http://rocq-prover.org/bugs/. *)

(** * Axioms for Opaque types *)

Axiom show_ident : Show Ident.ident.
Existing Instance show_ident.

Axiom show_var_info : Show var_info.
Existing Instance show_var_info.

(** NOTE: I am using [funname], not [FunName.t], because
    at extraction only [funname] is used/visible.

    TODO: for what other opaque types does this apply to? *)
Axiom show_funname : Show funname.
Existing Instance show_funname.

(** * Show Instances *)

(* TODO: organize by auto-generated and manually-written instances. *)

QCDerive Show for wsize.
QCDerive Show for positive.
QCDerive Show for atype.
Instance show_var : Show var :=
  {| show (x : var) :=
      match x with
      | {| vtype := p0; vname := p1 |} =>
          ("Var " ++ smart_paren (show p0) ++ " " ++ smart_paren (show p1))%string
      end |}.
Instance show_var_i : Show var_i :=
  {| show (x : var_i) :=
       match x with
       | {| v_var := p0; v_info := p1 |} =>
           ("VarI " ++ smart_paren (show p0) ++ " " ++ smart_paren (show p1))%string
       end |}.
QCDerive Show for v_scope.
Instance show_gvar : Show gvar :=
  {| show (x : gvar) :=
      match x with
      | {| gv := p0; gs := p1 |} =>
          ("Gvar " ++ smart_paren (show p0) ++ " " ++ smart_paren (show p1))%string
      end |}.
QCDerive Show for aligned.
QCDerive Show for arr_access.
QCDerive Show for signedness.
QCDerive Show for op_kind.
QCDerive Show for wiop1.
QCDerive Show for sop1.
QCDerive Show for cmp_kind.
QCDerive Show for velem.
QCDerive Show for wiop2.
QCDerive Show for sop2.
QCDerive Show for pelem.
QCDerive Show for combine_flags.
QCDerive Show for opN.

Print word.

(* QCDerive Show for word.word.word. *)

(* QCDerive Show for WArray.array. *)

(* QCDerive Show for word. *)

(* QCDerive Show for glob_value.  *)

(* But [Show] does exist for [list] ... *)
Fail QCDerive Show for pexpr.

Module example.
  (* Still fails if we explicitly add it? *)

  Global Instance show_pexprs `{Show pexpr} : Show (seq pexpr) := showList.
  Fail QCDerive Show for pexpr.

End example.

(** Shorthand to avoid maually writing [_ ++ " " ++ _ ++ ...]. *)
Notation show0 := (Basics.compose ShowFunctions.string_concat (ShowFunctions.intersperse " "%string)).

(** The body of [Show (list A)], needed for nested recursive instances. *)
Definition show__list {A : Type} (show_aux : A -> string) (xs : list A) : string :=
  append "[" (append (contents show_aux xs) "]").

(** FIXME: manually writing [Show expr] for now. *)
Fixpoint show_pexpr_aux (e : pexpr) : string := 
  match e with
  | Pconst z => "Pconst " ++ smart_paren (show z)
  | Pbool b => "Pbool " ++ smart_paren (show b)
  | Parr_init ws p => show0 ("Parr_init" :: map smart_paren [:: show ws; show p]) 
  | Pvar x => "Pvar " ++ smart_paren (show x)
  | Pget al aa ws x e => show0 ("Pget" :: map smart_paren [:: show al; show aa; show ws; show x; show_pexpr_aux e])
  | Psub aa ws len x e => show0 ("Pget" :: map smart_paren [:: show aa; show ws; show len; show x; show_pexpr_aux e])
  | Pload al sz e => show0 ("Pload" :: map smart_paren [:: show al; show sz; show_pexpr_aux e])
  | Papp1 op e =>  show0 ("Papp1" :: map smart_paren [:: show op; show_pexpr_aux e])
  | Papp2 op e1 e2 => show0 ("Papp2" :: map smart_paren [:: show op; show_pexpr_aux e1; show_pexpr_aux e2])
  | PappN op es => "PappN " ++ smart_paren (show op) ++ " " ++ show__list show_pexpr_aux es
  | Pif t e e1 e2 => show0 ("Pif" :: map smart_paren [:: show t; show_pexpr_aux e; show_pexpr_aux e1; show_pexpr_aux e2])
  end%string.

Global Instance show_pexpr : Show pexpr :=
  {| show := show_pexpr_aux |}.

QCDerive Show for opN_safety.
QCDerive Show for eassert.

Global Instance show_lval : Show lval :=
  {| show lv :=
      match lv with
      | Lnone p0 p1 =>
          ("Lnone " ++ smart_paren (show p0) ++ " " ++ smart_paren (show p1))%string
      | Lvar p0 => ("Lvar " ++ smart_paren (show p0))%string
      | Lmem p0 p1 p2 p3 =>
          ("Lmem " ++
             smart_paren (show p0) ++
             " " ++
             smart_paren (show p1) ++
             " " ++ smart_paren (show p2) ++ " " ++ smart_paren (show p3))%string
      | Laset p0 p1 p2 p3 p4 =>
          ("Laset " ++
             smart_paren (show p0) ++
             " " ++
             smart_paren (show p1) ++
             " " ++
             smart_paren (show p2) ++
             " " ++ smart_paren (show p3) ++ " " ++ smart_paren (show p4))%string
      | Lasub p0 p1 p2 p3 p4 =>
          ("Lasub " ++
             smart_paren (show p0) ++
             " " ++
             smart_paren (show p1) ++
             " " ++
             smart_paren (show p2) ++
             " " ++ smart_paren (show p3) ++ " " ++ smart_paren (show p4))%string
      end |}.

QCDerive Show for spill_op.
QCDerive Show for pseudo_operator.
QCDerive Show for slh_op.

Global Instance show_prim_x86_suffix : Show prim_x86_suffix :=
  {| show x :=
      match x with
      | PVp p0 => ("PVp " ++ smart_paren (show p0))%string
      | PVs p0 p1 => ("PVs " ++ smart_paren (show p0) ++ " " ++ smart_paren (show p1))%string
      | PVv p0 p1 => ("PVv " ++ smart_paren (show p0) ++ " " ++ smart_paren (show p1))%string
      | PVsv p0 p1 p2 =>
          ("PVsv " ++
             smart_paren (show p0) ++
             " " ++ smart_paren (show p1) ++ " " ++ smart_paren (show p2))%string
      | PVx p0 p1 => ("PVx " ++ smart_paren (show p0) ++ " " ++ smart_paren (show p1))%string
      | PVvv p0 p1 p2 p3 =>
          ("PVvv " ++
             smart_paren (show p0) ++
             " " ++
             smart_paren (show p1) ++
             " " ++ smart_paren (show p2) ++ " " ++ smart_paren (show p3))%string
      end |}.

(* Error: Case Not Handled *)
Fail QCDerive Show for prim_constructor.

(* Error: *)
(* Anomaly *)
(* "Uncaught exception Failure("Not a valid class name. Expected one of : GenSized , EnumSized , Shrink , Arbitrary , Show , Sized , DecOpt , ArbitrarySizedSuchThat , GenSizedSuchThat , EnumSizedSuchThat , Generator , Enumerator , Checker")." *)
(* Please report at http://rocq-prover.org/bugs/. *)
(* Fail QCDerive ShowFunctions.ReprSubset for prim_x86_suffix. *)

(* TODO: *)
Global Instance repr_prim_x86_suffix : ShowFunctions.ReprSubset prim_x86_suffix :=
  {| ShowFunctions.representatives := [::] |}.

Global Instance show_result {E A : Type} `{Show E, Show A} : Show (result E A) :=
  {| show r :=
      match r with
      | Ok _ x => "Ok " ++ smart_paren (show x)
      | Error x => "Error " ++ smart_paren (show x)
      end%string |}.

Global Instance show_prim_constructor {asm_op : Type} `{!Show asm_op}
  : Show (prim_constructor asm_op) :=
  {| show pc :=
      match pc with
      | PrimX86 prim_suffixes prim_suffix_fun =>
          "PrimX86 " ++ smart_paren (show prim_suffixes) ++ " " ++ smart_paren (show prim_suffix_fun)
      | PrimARM f =>
          "PrimARM " ++ smart_paren (show f)
      end%string |}.

QCDerive Show for assgn_tag.
QCDerive Show for syscall_t.
QCDerive Show for dir.

(* Error: Anomaly "Uncaught exception Failure("destIndRef")." *)
(* Please report at http://rocq-prover.org/bugs/. *)
(* Fail QCDerive Show for range. *)

(* FIXME: why doesn't [showPair] just work with this automatically? *)
Global Instance show_range : Show range :=
  {| show r := show r |}.

(* Bruh? *)
Fail QCDerive Show for align.

Global Instance show_align : Show align :=
  {| show a :=
      match a with
      | Align => "Align"
      | NoAlign => "NoAlign"
      end%string |}.

Section ASM_OP.
  Context {asm_op : Type} `{asmop : !asmOp asm_op}.

  (* TODO: is this correct? *)
  Context `{show_asm_op : !Show asm_op}.

  (* TODO: Do I need this? Because of the [asm_op_t] wrapper? *)
  (* Global Instance show_asm_op_t : Show asm_op_t := show_asm_op. *)

  Fail QCDerive Show for sopn.

  Global Instance show_sopn : Show sopn :=
    {| show o :=
        match o with
        | Opseudo_op o => "Opseudo_op " ++ smart_paren (show o)
        | Oslh o => "Oslh " ++ smart_paren (show o)
        | Oasm o => "Oasm " ++ smart_paren (show o)
        end%string |}.

(* Error: *)
(* In environment *)
(* asm_op : Type *)
(* asmop : asmOp asm_op *)
(* show_asm_op : Show asm_op *)
(* asm_op0 : Type *)
(* H : Show asm_op0 *)
(* asmop0 : Type *)
(* H0 : Show asmop0 *)
(* The term "asmop0" has type "Type" while it is expected to have type "asmOp asm_op0". *)
  Fail QCDerive Show for instr_r.

  Fixpoint show_instr_r_aux (i : instr_r) : string :=
    match i with
    | Cassgn lv tg t e =>
        show0 ("Cassgn" :: map smart_paren [:: show lv; show tg; show t; show e])
    | Copn lvs tg o es =>
        show0 ("Copn" :: map smart_paren [:: show lvs; show tg; show o; show es])
    | Csyscall lvs o es =>
        show0 ("Csyscall" :: map smart_paren [:: show lvs; show o; show es])
    | Cassert a => "Cassert " ++ smart_paren (show a)
    | Cif e c1 c2 =>
        show0 [:: "Cif"; smart_paren (show e); show__list show_instr_aux c1;  show__list show_instr_aux c2]
    | Cfor x r c =>
        show0 ("Cfor" :: map smart_paren [:: show x; show r] ++ [:: show__list show_instr_aux c])
    | Cwhile a c e ii c' =>
        (* NOTE: for now, throw away info *)
        show0 [:: "Cwhile"; smart_paren (show a); show__list show_instr_aux c; smart_paren (show e); show__list show_instr_aux c']
    | Ccall lvs f es =>
        show0 [:: "Ccall"; show lvs; show f; show es]
    end%string
  (* NOTE: for now, throwing away instruction info.
     Should I care about this?
     It just seems like noise... *)
  with show_instr_aux (i : instr) : string :=
         match i with
         | MkI _ i => show_instr_r_aux i
         end.

  Global Instance show_instr_r : Show instr_r :=
    {| show := show_instr_r_aux |}.

  Global Instance show_instr : Show instr :=
    {| show := show_instr_aux |}.

  Global Instance show_fun_contract : Show fun_contract :=
    {| show x :=
        match x with
        | {| f_iparams := p0; f_ires := p1; f_pre := p2; f_post := p3 |} =>
            ("MkContra " ++
               smart_paren (show p0) ++
               " " ++
               smart_paren (show p1) ++
               " " ++ smart_paren (show p2) ++ " " ++ smart_paren (show p3))%string
        end |}.

  Section extra_fun_t.
    Context `{!progT}.
    Context `{!Show extra_fun_t, !Show extra_prog_t, !Show extra_val_t}.

    Global Instance show_fundef : Show fundef :=
      {| show fd :=
          (* NOTE: ignoring [fun_info] for now. *)
          show0 ("MkFun"%string :: map smart_paren
                   [:: show fd.(f_contract);
                    show fd.(f_tyin);
                    show fd.(f_params);
                    show fd.(f_body);
                    show fd.(f_tyout);
                    show fd.(f_res);
                    show fd.(f_extra)]) |}.

    (* Fail QCDerive Show for fun_decl. *)
    Global Instance show_fun_decl : Show fun_decl :=
      {| show fd := show fd |}.

    Fail Global Instance show_prog : Show prog :=
      {| show p :=
          show0 ("Build__prog"%string :: map smart_paren
                   [:: show p.(p_funcs);
                    show p.(p_globs);
                    show p.(p_extra)]) |}.
  End extra_fun_t.
End ASM_OP.
