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

(* __shuffle4 *)
(* Local variables *)
Definition a_19093 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19093).
Definition b_19094 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19094).
Definition r0_19095 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19095).
Definition r1_19096 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19096).

(* Signature *)
Definition tyin___shuffle4 : seq atype := [:: aword U256; aword U256 ].
Definition args___shuffle4 : seq var_i := [:: a_19093.(gv); b_19094.(gv) ].
Definition tyout___shuffle4 : seq atype := [:: aword U256; aword U256 ].
Definition res___shuffle4 : seq var_i := [:: r0_19095.(gv); r1_19096.(gv) ].

(* Body *)
Definition body___shuffle4 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar r0_19095.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE64 U256))))) [:: Pvar a_19093
                                                                    ; Pvar b_19094 ])
    ; MkI dummy_instr_info (Copn [:: Lvar r1_19096.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U256))))) [:: Pvar a_19093
                                                                    ; Pvar b_19094 ]) ].

Definition fd___shuffle4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___shuffle4;
    f_params := args___shuffle4;
    f_body := body___shuffle4;
    f_tyout := tyout___shuffle4;
    f_res := res___shuffle4;
    f_extra := tt;
  |}.

End IDO.
