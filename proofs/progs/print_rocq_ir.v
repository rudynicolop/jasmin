From Jasmin Require Export oracles.
Require Export mathcomp.ssreflect.seq.

(** NOTE: This should export [Show] for lists? *)
Require Import QuickChick.QuickChick.

(*** Print Rocq IR *)

(** A (not pretty/ugly) printer for the Rocq-level Jasmin IR. *)

(* Fail QCDerive Show for _uprog. *)
(* Error: Anomaly "Uncaught exception Failure("destIndRef")." Please report at http://rocq-prover.org/bugs/. *)

QCDerive Show for wsize.
QCDerive Show for positive.
QCDerive Show for atype.
Axiom show_ident : Show Ident.ident.
Existing Instance show_ident.
Instance show_var : Show var :=
  {| show (x : var) :=
      match x with
      | {| vtype := p0; vname := p1 |} =>
          ("Var " ++ smart_paren (show p0) ++ " " ++ smart_paren (show p1))%string
      end |}.
Axiom show_var_info : Show var_info.
Existing Instance show_var_info.
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

(* But [Show] does exist for [list] ... *)
Fail QCDerive Show for pexpr.

Module example.
  (* Still fails if we explicitly add it? *)

  Global Instance show_pexprs `{Show pexpr} : Show (seq pexpr) := showList.
  Fail QCDerive Show for pexpr.

End example.

(** FIXME: manually writing [Show expr] for now. *)
Fixpoint show_pexpr_aux (e : pexpr) : string := 
  match e with
  | Pconst z => "Pconst " ++ smart_paren (show z)
  | Pbool b => "Pbool " ++ smart_paren (show b)
  | Parr_init ws p => "Parr_init " ++ smart_paren (show ws) ++ " " ++ smart_paren (show p) 
  | Pvar x => "Pvar " ++ smart_paren (show x)
  | Pget al aa ws x e => "Pget " ++ smart_paren (show al) ++ " "  ++ smart_paren (show aa) ++ " "  ++ smart_paren (show ws) ++ " "  ++ smart_paren (show x) ++ " "  ++ smart_paren (show_pexpr_aux e)
  | Psub aa ws len x e => "Psub " ++ smart_paren (show aa) ++ " "  ++ smart_paren (show ws) ++ " "  ++ smart_paren (show len) ++ " "  ++ smart_paren (show x) ++ " "  ++ smart_paren (show_pexpr_aux e)
  | Pload al sz e => "Pload " ++ smart_paren (show al) ++ " "  ++ smart_paren (show sz) ++ " "  ++ smart_paren (show_pexpr_aux e)
  | Papp1 op e => "Papp1 " ++ smart_paren (show op) ++ " " ++ smart_paren (show_pexpr_aux e)
  | Papp2 op e1 e2 => "Papp2 " ++ smart_paren (show op) ++ " " ++ smart_paren (show_pexpr_aux e1) ++ " " ++ smart_paren (show_pexpr_aux e2)
  | PappN op es => "PappN " ++ smart_paren (show op) ++ " " ++ append "[" (append (contents show_pexpr_aux es) "]")
  | Pif t e e1 e2 => "Pif " ++ smart_paren (show t) ++ " " ++ smart_paren (show_pexpr_aux e) ++ " " ++ smart_paren (show_pexpr_aux e1) ++ " " ++ smart_paren (show_pexpr_aux e2)
  end%string.
