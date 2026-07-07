From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Axiom IdO : IdentOracles.
Existing Instance IdO.

(* -------------------------------------------------------------------------- *)
(* Globals *)

Definition identity_prog_gds : glob_decls := [::].

(* -------------------------------------------------------------------------- *)
(* Function names *)

Definition identity : funname := mkfname 154.

(* -------------------------------------------------------------------------- *)
(* Functions *)

(* identity *)
(* Local variables *)
Definition x : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 157).
Definition r : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 158).

(* Signature *)
Definition tyin_identity : seq atype := [:: aword U64 ].
Definition args_identity : seq var_i := [:: x.(gv) ].
Definition tyout_identity : seq atype := [:: aword U64 ].
Definition res_identity : seq var_i := [:: r.(gv) ].

(* Body *)
Definition body_identity : cmd :=
  [:: cassgn (Lvar r.(gv)) (aword U64) (Pvar x) ].

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

(* -------------------------------------------------------------------------- *)
(* Program *)

Definition identity_prog : uprog :=
  {|
    p_globs := identity_prog_gds;
    p_funcs := [:: (identity, fd_identity) ];
    p_extra := tt;
  |}.
