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

(* A1____dumpstate_avx2 *)
(* Local variables *)
Definition buf_24 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18201).
Definition offset_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18202).
Definition _LEN_11 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18203).
Definition st_18 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 18204).
Definition DELTA_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18205).
Definition t128_0_4 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18206).
Definition t128_1_6 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18207).
Definition t_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18208).
Definition t256_0_4 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18209).
Definition t256_1_4 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18210).
Definition t256_2_4 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18211).
Definition t256_3_2 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18212).
Definition t256_4_1 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18213).

(* Signature *)
Definition tyin_A1____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1; aword U64; aint; aarr U256 7 ].
Definition args_A1____dumpstate_avx2 : seq var_i :=
  [:: buf_24.(gv); offset_8.(gv); _LEN_11.(gv); st_18.(gv) ].
Definition tyout_A1____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1; aword U64 ].
Definition res_A1____dumpstate_avx2 : seq var_i :=
  [:: buf_24.(gv); offset_8.(gv) ].

(* Body *)
Definition body_A1____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_7.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_11))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_24.(gv)
                                                                ; Lvar DELTA_7.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A1____a_ilen_write_upto32 [:: Pvar buf_24
                                                                    ; Pvar offset_8
                                                                    ; Pvar DELTA_7
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_18 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_11.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_11) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_24.(gv)
                                                                ; Lvar DELTA_7.(gv)
                                                                ; Lvar _LEN_11.(gv) ] A1____a_ilen_write_upto32 [:: Pvar buf_24
                                                                    ; Pvar offset_8
                                                                    ; Pvar DELTA_7
                                                                    ; Pvar _LEN_11
                                                                    ; Pget Aligned AAscale U256 st_18 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_24.(gv)
                                    ; Lvar DELTA_7.(gv)
                                    ; Lvar _LEN_11.(gv) ] A1____a_ilen_write_upto32 [:: Pvar buf_24
                                                                    ; Pvar offset_8
                                                                    ; Pvar DELTA_7
                                                                    ; Pvar _LEN_11
                                                                    ; Pget Aligned AAscale U256 st_18 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_11))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_4.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_18 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_6.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_18 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_3.(gv)) AT_none (aword U64) (Pvar t128_1_6))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_24.(gv)
                                                                ; Lvar DELTA_7.(gv)
                                                                ; Lvar _LEN_11.(gv) ] A1____a_ilen_write_upto8 [:: Pvar buf_24
                                                                    ; Pvar offset_8
                                                                    ; Pvar DELTA_7
                                                                    ; Pvar _LEN_11
                                                                    ; Pvar t_3 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_6
                                                                    ; Pvar t128_1_6 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_11))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_18 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_18 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_18 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_18 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_18 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_18 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_18 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_18 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_4
                                                                    ; Pvar t256_3_2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_24.(gv)
                                                                  ; Lvar DELTA_7.(gv)
                                                                  ; Lvar _LEN_11.(gv) ] A1____a_ilen_write_upto32 [:: Pvar buf_24
                                                                    ; Pvar offset_8
                                                                    ; Pvar DELTA_7
                                                                    ; Pvar _LEN_11
                                                                    ; Pvar t256_4_1 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_11))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_3.(gv)) AT_none (aword U64) (Pvar t128_0_4))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_24.(gv)
                                                                    ; Lvar DELTA_7.(gv)
                                                                    ; Lvar _LEN_11.(gv) ] A1____a_ilen_write_upto8 [:: Pvar buf_24
                                                                    ; Pvar offset_8
                                                                    ; Pvar DELTA_7
                                                                    ; Pvar _LEN_11
                                                                    ; Pvar t_3 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_4
                                                                    ; Pvar t128_0_4 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_11))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_2
                                                                    ; Pvar t256_1_4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_24.(gv)
                                                                    ; Lvar DELTA_7.(gv)
                                                                    ; Lvar _LEN_11.(gv) ] A1____a_ilen_write_upto32 [:: Pvar buf_24
                                                                    ; Pvar offset_8
                                                                    ; Pvar DELTA_7
                                                                    ; Pvar _LEN_11
                                                                    ; Pvar t256_4_1 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_11))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_3.(gv)) AT_none (aword U64) (Pvar t128_1_6))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_24.(gv)
                                                                    ; Lvar DELTA_7.(gv)
                                                                    ; Lvar _LEN_11.(gv) ] A1____a_ilen_write_upto8 [:: Pvar buf_24
                                                                    ; Pvar offset_8
                                                                    ; Pvar DELTA_7
                                                                    ; Pvar _LEN_11
                                                                    ; Pvar t_3 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_11))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_4
                                                                    ; Pvar t256_0_4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_24.(gv)
                                                                    ; Lvar DELTA_7.(gv)
                                                                    ; Lvar _LEN_11.(gv) ] A1____a_ilen_write_upto32 [:: Pvar buf_24
                                                                    ; Pvar offset_8
                                                                    ; Pvar DELTA_7
                                                                    ; Pvar _LEN_11
                                                                    ; Pvar t256_4_1 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_11))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_3.(gv)) AT_none (aword U64) (Pvar t128_0_4))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_24.(gv)
                                                                    ; Lvar DELTA_7.(gv)
                                                                    ; Lvar _LEN_11.(gv) ] A1____a_ilen_write_upto8 [:: Pvar buf_24
                                                                    ; Pvar offset_8
                                                                    ; Pvar DELTA_7
                                                                    ; Pvar _LEN_11
                                                                    ; Pvar t_3 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_11))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_4
                                                                    ; Pvar t256_2_4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_24.(gv)
                                                                    ; Lvar DELTA_7.(gv)
                                                                    ; Lvar _LEN_11.(gv) ] A1____a_ilen_write_upto32 [:: Pvar buf_24
                                                                    ; Pvar offset_8
                                                                    ; Pvar DELTA_7
                                                                    ; Pvar _LEN_11
                                                                    ; Pvar t256_4_1 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_8.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_7)))) ].

Definition fd_A1____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____dumpstate_avx2;
    f_params := args_A1____dumpstate_avx2;
    f_body := body_A1____dumpstate_avx2;
    f_tyout := tyout_A1____dumpstate_avx2;
    f_res := res_A1____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
