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

(* __u256x4_4u64x4 *)
(* Local variables *)
Definition x0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18640).
Definition x1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18641).
Definition x2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18642).
Definition x3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18643).
Definition y0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18644).
Definition y1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18645).
Definition y2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18646).
Definition y3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18647).

(* Signature *)
Definition tyin___u256x4_4u64x4 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition args___u256x4_4u64x4 : seq var_i :=
  [:: x0.(gv); x1.(gv); x2.(gv); x3.(gv) ].
Definition tyout___u256x4_4u64x4 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition res___u256x4_4u64x4 : seq var_i :=
  [:: x0.(gv); x1.(gv); x2.(gv); x3.(gv) ].

(* Body *)
Definition body___u256x4_4u64x4 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar y0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE64 U256))))) [:: Pvar x0
                                                                    ; Pvar x1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar y1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U256))))) [:: Pvar x0
                                                                    ; Pvar x1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar y2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE64 U256))))) [:: Pvar x2
                                                                    ; Pvar x3 ])
    ; MkI dummy_instr_info (Copn [:: Lvar y3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U256))))) [:: Pvar x2
                                                                    ; Pvar x3 ])
    ; MkI dummy_instr_info (Copn [:: Lvar x0.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y0
                                                                    ; Pvar y2
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar x1.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y1
                                                                    ; Pvar y3
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar x2.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y0
                                                                    ; Pvar y2
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (49)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar x3.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y1
                                                                    ; Pvar y3
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (49)%Z) ]) ].

Definition fd___u256x4_4u64x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___u256x4_4u64x4;
    f_params := args___u256x4_4u64x4;
    f_body := body___u256x4_4u64x4;
    f_tyout := tyout___u256x4_4u64x4;
    f_res := res___u256x4_4u64x4;
    f_extra := tt;
  |}.

End IDO.
