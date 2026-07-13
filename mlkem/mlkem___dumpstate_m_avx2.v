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

(* __dumpstate_m_avx2 *)
(* Local variables *)
Definition buf_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18764).
Definition _LEN_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18765).
Definition st_6 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 18766).
Definition t128_0_2 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18767).
Definition t128_1_3 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18768).
Definition t_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18769).
Definition t256_0_3 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18770).
Definition t256_1_3 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18771).
Definition t256_2_3 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18772).
Definition t256_3_1 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18773).
Definition t256_4_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18774).

(* Signature *)
Definition tyin___dumpstate_m_avx2 : seq atype :=
  [:: aword U64; aint; aarr U256 7 ].
Definition args___dumpstate_m_avx2 : seq var_i :=
  [:: buf_10.(gv); _LEN_1.(gv); st_6.(gv) ].
Definition tyout___dumpstate_m_avx2 : seq atype := [:: aword U64 ].
Definition res___dumpstate_m_avx2 : seq var_i := [:: buf_10.(gv) ].

(* Body *)
Definition body___dumpstate_m_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_1))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_10.(gv)
                                                                ; Lnone dummy_var_info (aint) ] __m_ilen_write_upto32 [:: Pvar buf_10
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_6 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_1.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_1) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_10.(gv)
                                                                ; Lvar _LEN_1.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_10
                                                                    ; Pvar _LEN_1
                                                                    ; Pget Aligned AAscale U256 st_6 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_10.(gv); Lvar _LEN_1.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_10
                                                                    ; Pvar _LEN_1
                                                                    ; Pget Aligned AAscale U256 st_6 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_1))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_2.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_6 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_3.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_6 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_1.(gv)) AT_none (aword U64) (Pvar t128_1_3))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_10.(gv)
                                                                ; Lvar _LEN_1.(gv) ] __m_ilen_write_upto8 [:: Pvar buf_10
                                                                    ; Pvar _LEN_1
                                                                    ; Pvar t_1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_3
                                                                    ; Pvar t128_1_3 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_1))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_6 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_6 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_6 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_6 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_6 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_6 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_6 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_6 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_3
                                                                    ; Pvar t256_3_1
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_10.(gv)
                                                                  ; Lvar _LEN_1.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_10
                                                                    ; Pvar _LEN_1
                                                                    ; Pvar t256_4_0 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_1))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_1.(gv)) AT_none (aword U64) (Pvar t128_0_2))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_10.(gv)
                                                                    ; Lvar _LEN_1.(gv) ] __m_ilen_write_upto8 [:: Pvar buf_10
                                                                    ; Pvar _LEN_1
                                                                    ; Pvar t_1 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_2
                                                                    ; Pvar t128_0_2 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_1))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_1
                                                                    ; Pvar t256_1_3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_10.(gv)
                                                                    ; Lvar _LEN_1.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_10
                                                                    ; Pvar _LEN_1
                                                                    ; Pvar t256_4_0 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_1))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_1.(gv)) AT_none (aword U64) (Pvar t128_1_3))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_10.(gv)
                                                                    ; Lvar _LEN_1.(gv) ] __m_ilen_write_upto8 [:: Pvar buf_10
                                                                    ; Pvar _LEN_1
                                                                    ; Pvar t_1 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_1))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_3
                                                                    ; Pvar t256_0_3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_10.(gv)
                                                                    ; Lvar _LEN_1.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_10
                                                                    ; Pvar _LEN_1
                                                                    ; Pvar t256_4_0 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_1))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_1.(gv)) AT_none (aword U64) (Pvar t128_0_2))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_10.(gv)
                                                                    ; Lvar _LEN_1.(gv) ] __m_ilen_write_upto8 [:: Pvar buf_10
                                                                    ; Pvar _LEN_1
                                                                    ; Pvar t_1 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_1))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_3
                                                                    ; Pvar t256_2_3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_10.(gv)
                                                                    ; Lvar _LEN_1.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_10
                                                                    ; Pvar _LEN_1
                                                                    ; Pvar t256_4_0 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::]) ].

Definition fd___dumpstate_m_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___dumpstate_m_avx2;
    f_params := args___dumpstate_m_avx2;
    f_body := body___dumpstate_m_avx2;
    f_tyout := tyout___dumpstate_m_avx2;
    f_res := res___dumpstate_m_avx2;
    f_extra := tt;
  |}.

End IDO.
