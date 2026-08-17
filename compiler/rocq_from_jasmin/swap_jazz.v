From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Axiom IdO : IdentOracles.
Existing Instance IdO.

(* -------------------------------------------------------------------------- *)
(* Globals *)

Definition swap_prog_gds : glob_decls := [::].

(* -------------------------------------------------------------------------- *)
(* Function names *)

Definition swap : funname := mkfname 154.
Definition run_swap : funname := mkfname 163.

(* -------------------------------------------------------------------------- *)
(* Functions *)

(* swap *)
(* Local variables *)
Definition x : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 173).
Definition y : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 174).
Definition z : gvar := mk_rocq_gvar Slocal (aword U32) (mkident 175).

(* Signature *)
Definition tyin_swap : seq atype := [:: aword U64; aword U64 ].
Definition args_swap : seq var_i := [:: x.(gv); y.(gv) ].
Definition tyout_swap : seq atype := [::].
Definition res_swap : seq var_i := [::].

(* Body *)
Definition body_swap : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar z.(gv)) AT_none (aword U32) (Pload Unaligned U32 (Pvar x)))
    ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U32 dummy_var_info (Pvar x)) AT_none (aword U32) (Pload Unaligned U32 (Pvar y)))
    ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U32 dummy_var_info (Pvar y)) AT_none (aword U32) (Pvar z)) ].

Definition fd_swap : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_swap;
    f_params := args_swap;
    f_body := body_swap;
    f_tyout := tyout_swap;
    f_res := res_swap;
    f_extra := tt;
  |}.

(* run_swap *)
(* Local variables *)
Definition x_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 170).
Definition y_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 171).
Definition n : gvar := mk_rocq_gvar Slocal (aword U32) (mkident 172).

(* Signature *)
Definition tyin_run_swap : seq atype := [:: aword U64; aword U64 ].
Definition args_run_swap : seq var_i := [:: x_0.(gv); y_0.(gv) ].
Definition tyout_run_swap : seq atype := [:: aword U32 ].
Definition res_run_swap : seq var_i := [:: n.(gv) ].

(* Body *)
Definition body_run_swap : cmd :=
  [:: MkI dummy_instr_info (Ccall [::] swap [:: Pvar x_0; Pvar y_0 ])
    ; MkI dummy_instr_info (Cassgn (Lvar n.(gv)) AT_none (aword U32) (Pload Unaligned U32 (Pvar y_0))) ].

Definition fd_run_swap : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_run_swap;
    f_params := args_run_swap;
    f_body := body_run_swap;
    f_tyout := tyout_run_swap;
    f_res := res_run_swap;
    f_extra := tt;
  |}.

(* -------------------------------------------------------------------------- *)
(* Program *)

Definition swap_prog : uprog :=
  {|
    p_globs := swap_prog_gds;
    p_funcs := [:: (swap, fd_swap); (run_swap, fd_run_swap) ];
    p_extra := tt;
  |}.
