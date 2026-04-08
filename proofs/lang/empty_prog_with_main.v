From Jasmin Require Export hoare_logic.
From Jasmin Require Import it_sems_core core_logics.
From Jasmin Require Import expr oseq psem_core.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import Stdlib.micromega.Lia.

Definition FInfo_witness : fun_info := FunInfo.witness.

Section prog.
  Context {pd: PointerData} `{asmop:asmOp}.

  (** Get function name identifiers. *)
  Context (to_funname : string -> FunName.t).

  Definition main_def : _fundef unit :=
    {| f_info := (FInfo_witness : fun_info)
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
    (to_funname "main", main_def).

  Definition empty_prog : _uprog :=
    {|
      p_funcs := [:: main_decl];
      (* No globals *)
      p_globs := [::];
      p_extra := tt;

  |}.
End prog.
