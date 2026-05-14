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
Definition buf_18764 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18764).
Definition _LEN_18765 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18765).
Definition st_18766 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 18766).
Definition t128_0_18767 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18767).
Definition t128_1_18768 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18768).
Definition t_18769 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18769).
Definition t256_0_18770 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18770).
Definition t256_1_18771 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18771).
Definition t256_2_18772 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18772).
Definition t256_3_18773 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18773).
Definition t256_4_18774 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18774).

(* Signature *)
Definition tyin___dumpstate_m_avx2 : seq atype :=
  [:: aword U64; aint; aarr U256 7 ].
Definition args___dumpstate_m_avx2 : seq var_i :=
  [:: buf_18764.(gv); _LEN_18765.(gv); st_18766.(gv) ].
Definition tyout___dumpstate_m_avx2 : seq atype := [:: aword U64 ].
Definition res___dumpstate_m_avx2 : seq var_i := [:: buf_18764.(gv) ].

(* Body *)
Definition body___dumpstate_m_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_18765))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_18764.(gv)
                                                                ; Lnone dummy_var_info (aint) ] __m_ilen_write_upto32 [:: Pvar buf_18764
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_18766 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_18765.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_18765) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_18764.(gv)
                                                                ; Lvar _LEN_18765.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_18764
                                                                    ; Pvar _LEN_18765
                                                                    ; Pget Aligned AAscale U256 st_18766 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_18764.(gv)
                                    ; Lvar _LEN_18765.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_18764
                                                                    ; Pvar _LEN_18765
                                                                    ; Pget Aligned AAscale U256 st_18766 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18765))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_18767.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_18766 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_18768.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_18766 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_18769.(gv)) AT_none (aword U64) (Pvar t128_1_18768))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_18764.(gv)
                                                                ; Lvar _LEN_18765.(gv) ] __m_ilen_write_upto8 [:: Pvar buf_18764
                                                                    ; Pvar _LEN_18765
                                                                    ; Pvar t_18769 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_18768.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_18768
                                                                    ; Pvar t128_1_18768 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18765))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_18770.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_18766 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_18766 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_18771.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_18766 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_18766 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_18772.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_18766 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_18766 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_18773.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_18766 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_18766 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_18774.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_18770
                                                                    ; Pvar t256_3_18773
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_18764.(gv)
                                                                  ; Lvar _LEN_18765.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_18764
                                                                    ; Pvar _LEN_18765
                                                                    ; Pvar t256_4_18774 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18765))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_18769.(gv)) AT_none (aword U64) (Pvar t128_0_18767))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_18764.(gv)
                                                                    ; Lvar _LEN_18765.(gv) ] __m_ilen_write_upto8 [:: Pvar buf_18764
                                                                    ; Pvar _LEN_18765
                                                                    ; Pvar t_18769 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_18767.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_18767
                                                                    ; Pvar t128_0_18767 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18765))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_18774.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_18773
                                                                    ; Pvar t256_1_18771
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_18764.(gv)
                                                                    ; Lvar _LEN_18765.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_18764
                                                                    ; Pvar _LEN_18765
                                                                    ; Pvar t256_4_18774 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18765))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_18769.(gv)) AT_none (aword U64) (Pvar t128_1_18768))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_18764.(gv)
                                                                    ; Lvar _LEN_18765.(gv) ] __m_ilen_write_upto8 [:: Pvar buf_18764
                                                                    ; Pvar _LEN_18765
                                                                    ; Pvar t_18769 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18765))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_18774.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_18772
                                                                    ; Pvar t256_0_18770
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_18764.(gv)
                                                                    ; Lvar _LEN_18765.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_18764
                                                                    ; Pvar _LEN_18765
                                                                    ; Pvar t256_4_18774 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18765))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_18769.(gv)) AT_none (aword U64) (Pvar t128_0_18767))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_18764.(gv)
                                                                    ; Lvar _LEN_18765.(gv) ] __m_ilen_write_upto8 [:: Pvar buf_18764
                                                                    ; Pvar _LEN_18765
                                                                    ; Pvar t_18769 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18765))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_18774.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_18771
                                                                    ; Pvar t256_2_18772
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_18764.(gv)
                                                                    ; Lvar _LEN_18765.(gv) ] __m_ilen_write_upto32 [:: Pvar buf_18764
                                                                    ; Pvar _LEN_18765
                                                                    ; Pvar t256_4_18774 ]) ]
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
