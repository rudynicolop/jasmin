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

Definition identity_prog_gds : glob_decls := [::].

(* -------------------------------------------------------------------------- *)
(* Function names *)

Definition identity : funname := mkfname 153.
Definition main : funname := mkfname 161.

(* -------------------------------------------------------------------------- *)
(* Functions *)

(* identity *)
(* Local variables *)
Definition x : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 168).
Definition r : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 169).

(* Signature *)
Definition tyin_identity : seq atype := [:: aword U64 ].
Definition args_identity : seq var_i := [:: x.(gv) ].
Definition tyout_identity : seq atype := [:: aword U64 ].
Definition res_identity : seq var_i := [:: r.(gv) ].

(* Body *)
Definition body_identity : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar r.(gv)) AT_none (aword U64) (Pvar x)) ].

Definition fd_identity : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_identity;
    f_params := args_identity;
    f_body := body_identity;
    f_tyout := tyout_identity;
    f_res := res_identity;
    f_extra := tt;
  |}.

(* main *)
(* Local variables *)
Definition x_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 166).
Definition r_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 167).

(* Signature *)
Definition tyin_main : seq atype := [:: aword U64 ].
Definition args_main : seq var_i := [:: x_0.(gv) ].
Definition tyout_main : seq atype := [:: aword U64 ].
Definition res_main : seq var_i := [:: r_0.(gv) ].

(* Body *)
Definition body_main : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar r_0.(gv) ] identity [:: Papp2 (Oadd (Op_w U64)) (Pvar x_0) (Papp1 (Oword_of_int U64) (Pconst (1)%Z)) ])
    ; MkI dummy_instr_info (Cassgn (Lvar r_0.(gv)) AT_none (aword U64) (Papp2 (Omul (Op_w U64)) (Pvar r_0) (Papp1 (Oword_of_int U64) (Pconst (2)%Z)))) ].

Definition fd_main : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_main;
    f_params := args_main;
    f_body := body_main;
    f_tyout := tyout_main;
    f_res := res_main;
    f_extra := tt;
  |}.

(* -------------------------------------------------------------------------- *)
(* Program *)

Definition identity_prog : uprog :=
  {|
    p_globs := identity_prog_gds;
    p_funcs := [:: (identity, fd_identity); (main, fd_main) ];
    p_extra := tt;
  |}.
