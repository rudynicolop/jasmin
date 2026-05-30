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

(* __4u64x4_u256x4 *)
(* Local variables *)
Definition y0_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18612).
Definition y1_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18613).
Definition y2_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18614).
Definition y3_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18615).
Definition x0_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18616).
Definition x1_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18617).
Definition x2_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18618).
Definition x3_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18619).

(* Signature *)
Definition tyin___4u64x4_u256x4 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition args___4u64x4_u256x4 : seq var_i :=
  [:: y0_0.(gv); y1_0.(gv); y2_0.(gv); y3_0.(gv) ].
Definition tyout___4u64x4_u256x4 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition res___4u64x4_u256x4 : seq var_i :=
  [:: y0_0.(gv); y1_0.(gv); y2_0.(gv); y3_0.(gv) ].

(* Body *)
Definition body___4u64x4_u256x4 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar x0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y0_0
                                                                    ; Pvar y2_0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar x1_1.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y1_0
                                                                    ; Pvar y3_0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar x2_1.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y0_0
                                                                    ; Pvar y2_0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (49)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar x3_1.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y1_0
                                                                    ; Pvar y3_0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (49)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar y0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE64 U256))))) [:: Pvar x0_1
                                                                    ; Pvar x1_1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar y1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U256))))) [:: Pvar x0_1
                                                                    ; Pvar x1_1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar y2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE64 U256))))) [:: Pvar x2_1
                                                                    ; Pvar x3_1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar y3_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U256))))) [:: Pvar x2_1
                                                                    ; Pvar x3_1 ]) ].

Definition fd___4u64x4_u256x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___4u64x4_u256x4;
    f_params := args___4u64x4_u256x4;
    f_body := body___4u64x4_u256x4;
    f_tyout := tyout___4u64x4_u256x4;
    f_res := res___4u64x4_u256x4;
    f_extra := tt;
  |}.

End IDO.
