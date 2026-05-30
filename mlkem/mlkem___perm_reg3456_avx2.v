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

(* __perm_reg3456_avx2 *)
(* Local variables *)
Definition r3_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18850).
Definition r4_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18851).
Definition r5_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18852).
Definition r6_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18853).
Definition st3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18854).
Definition st4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18855).
Definition st5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18856).
Definition st6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18857).
Definition t256_0_1 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18858).
Definition t256_1_1 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18859).
Definition t256_2_1 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18860).

(* Signature *)
Definition tyin___perm_reg3456_avx2 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition args___perm_reg3456_avx2 : seq var_i :=
  [:: r3_1.(gv); r4_1.(gv); r5_1.(gv); r6_1.(gv) ].
Definition tyout___perm_reg3456_avx2 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition res___perm_reg3456_avx2 : seq var_i :=
  [:: st3.(gv); st4.(gv); st5.(gv); st6.(gv) ].

(* Body *)
Definition body___perm_reg3456_avx2 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar t256_0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar r3_1
                                                                    ; Pvar r5_1
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_1_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar r6_1
                                                                    ; Pvar r4_1
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_2_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar r4_1
                                                                    ; Pvar r3_1
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar st3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_1
                                                                    ; Pvar t256_1_1
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar st4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_1
                                                                    ; Pvar t256_0_1
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar r5_1
                                                                    ; Pvar r6_1
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar st5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_1
                                                                    ; Pvar t256_2_1
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar st6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_1
                                                                    ; Pvar t256_0_1
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]) ].

Definition fd___perm_reg3456_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___perm_reg3456_avx2;
    f_params := args___perm_reg3456_avx2;
    f_body := body___perm_reg3456_avx2;
    f_tyout := tyout___perm_reg3456_avx2;
    f_res := res___perm_reg3456_avx2;
    f_extra := tt;
  |}.

End IDO.
