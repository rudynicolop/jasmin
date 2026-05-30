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

(* __SHLQ_256 *)
(* Local variables *)
Definition x_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18987).
Definition shbytes_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18988).

(* Signature *)
Definition tyin___SHLQ_256 : seq atype := [:: aword U256; aint ].
Definition args___SHLQ_256 : seq var_i := [:: x_6.(gv); shbytes_1.(gv) ].
Definition tyout___SHLQ_256 : seq atype := [:: aword U256 ].
Definition res___SHLQ_256 : seq var_i := [:: x_6.(gv) ].

(* Body *)
Definition body___SHLQ_256 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar shbytes_1) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Copn [:: Lvar x_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pvar x_6
                                                                    ; Papp1 (Oword_of_int U128) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar shbytes_1)) ]) ]
                              [::]) ].

Definition fd___SHLQ_256 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___SHLQ_256;
    f_params := args___SHLQ_256;
    f_body := body___SHLQ_256;
    f_tyout := tyout___SHLQ_256;
    f_res := res___SHLQ_256;
    f_extra := tt;
  |}.

End IDO.
