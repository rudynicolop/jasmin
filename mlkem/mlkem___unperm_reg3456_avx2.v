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

(* __unperm_reg3456_avx2 *)
(* Local variables *)
Definition st3_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18838).
Definition st4_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18839).
Definition st5_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18840).
Definition st6_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18841).
Definition r3_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18842).
Definition r4_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18843).
Definition r5_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18844).
Definition r6_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18845).
Definition t256_0_2 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18846).
Definition t256_1_2 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18847).
Definition t256_2_2 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18848).
Definition t256_3_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18849).

(* Signature *)
Definition tyin___unperm_reg3456_avx2 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition args___unperm_reg3456_avx2 : seq var_i :=
  [:: st3_0.(gv); st4_0.(gv); st5_0.(gv); st6_0.(gv) ].
Definition tyout___unperm_reg3456_avx2 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition res___unperm_reg3456_avx2 : seq var_i :=
  [:: r3_2.(gv); r4_2.(gv); r5_2.(gv); r6_2.(gv) ].

(* Body *)
Definition body___unperm_reg3456_avx2 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar t256_0_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar st3_0
                                                                    ; Pvar st4_0
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_1_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar st4_0
                                                                    ; Pvar st3_0
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_2_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar st5_0
                                                                    ; Pvar st6_0
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_3_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar st6_0
                                                                    ; Pvar st5_0
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar r3_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_2
                                                                    ; Pvar t256_3_0
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar r4_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_0
                                                                    ; Pvar t256_1_2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar r5_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_2
                                                                    ; Pvar t256_0_2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar r6_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_2
                                                                    ; Pvar t256_2_2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]) ].

Definition fd___unperm_reg3456_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___unperm_reg3456_avx2;
    f_params := args___unperm_reg3456_avx2;
    f_body := body___unperm_reg3456_avx2;
    f_tyout := tyout___unperm_reg3456_avx2;
    f_res := res___unperm_reg3456_avx2;
    f_extra := tt;
  |}.

End IDO.
