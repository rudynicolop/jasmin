From Jasmin Require Export hoare_logic.
From Jasmin Require Import it_sems_core core_logics.
From Jasmin Require Import expr oseq psem_core.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import Stdlib.micromega.Lia.

Section prog.
  Context {pd: PointerData} `{asmop:asmOp}.

  Context

    (** Get function name identifiers.
        NOTE: It is *CRITICAL* that we use [funname] here, no
        [FunName.t], which is hidden after extraction! *)
    (to_funname : string -> funname)

    (** Dummy function info
        Yes, [FunInfo.witness] is completely useless, since
        extraction hides the type [t] of extracted [FunInfo.t] under a
        module signature, OCaml expects parameter [f_info] to have
        type [fun_info = FInfo.t], not [fun_info = FunInfo.t]... yikes... *)
    (fun_info_dummy : fun_info)
  .

  Definition main_def : _fundef unit :=
    {| f_info := fun_info_dummy
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
