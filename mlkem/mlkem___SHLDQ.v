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

(* __SHLDQ *)
(* Local variables *)
Definition x_5 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18989).
Definition shbytes_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18990).

(* Signature *)
Definition tyin___SHLDQ : seq atype := [:: aword U128; aint ].
Definition args___SHLDQ : seq var_i := [:: x_5.(gv); shbytes_0.(gv) ].
Definition tyout___SHLDQ : seq atype := [:: aword U128 ].
Definition res___SHLDQ : seq var_i := [:: x_5.(gv) ].

(* Body *)
Definition body___SHLDQ : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar shbytes_0) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Copn [:: Lvar x_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLLDQ U128))))) [:: Pvar x_5
                                                                    ; Papp1 (Oword_of_int U8) (Pvar shbytes_0) ]) ]
                              [::]) ].

Definition fd___SHLDQ : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___SHLDQ;
    f_params := args___SHLDQ;
    f_body := body___SHLDQ;
    f_tyout := tyout___SHLDQ;
    f_res := res___SHLDQ;
    f_extra := tt;
  |}.

End IDO.
