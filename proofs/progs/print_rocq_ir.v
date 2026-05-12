From Jasmin Require Export oracles.
Require Export mathcomp.ssreflect.seq.

(** NOTE: This should export [Show] for lists? *)
Require Import QuickChick.QuickChick.

(*** Print Rocq IR *)

(** A (not pretty/ugly) printer for the Rocq-level Jasmin IR. *)

(* Fail QCDerive Show for _uprog. *)
(* Error: Anomaly "Uncaught exception Failure("destIndRef")." Please report at http://rocq-prover.org/bugs/. *)

Fail QCDerive Show for pexpr.
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
QCDerive Show for wsize.
QCDerive Show for positive.
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
Instance show_seq {A : Type} `{Show A} : Show (seq A) :=
  showList.
(* Bruh *)
Fail QCDerive Show for pexpr.
