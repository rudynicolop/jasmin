From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* __SHLQ *)
(* Local variables *)
Definition x_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18991).
Definition shbytes : gvar := mk_rocq_gvar Slocal (aint) (mkident 18992).

(* Signature *)
Definition tyin___SHLQ : seq atype := [:: aword U64; aint ].
Definition args___SHLQ : seq var_i := [:: x_4.(gv); shbytes.(gv) ].
Definition tyout___SHLQ : seq atype := [:: aword U64 ].
Definition res___SHLQ : seq var_i := [:: x_4.(gv) ].

(* Body *)
Definition body___SHLQ : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar shbytes) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar x_4.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_4) (Papp1 (Oword_of_int U8) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar shbytes))))) ]
                              [::]) ].

Definition fd___SHLQ : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___SHLQ;
    f_params := args___SHLQ;
    f_body := body___SHLQ;
    f_tyout := tyout___SHLQ;
    f_res := res___SHLQ;
    f_extra := tt;
  |}.

End IDO.
