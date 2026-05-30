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

(* A128____dumpstate_avx2 *)
(* Local variables *)
Definition buf_92 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16426).
Definition offset_87 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16427).
Definition _LEN_55 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16428).
Definition st_62 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16429).
Definition DELTA_60 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16430).
Definition t128_0_14 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16431).
Definition t128_1_21 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16432).
Definition t_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16433).
Definition t256_0_9 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16434).
Definition t256_1_9 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16435).
Definition t256_2_9 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16436).
Definition t256_3_7 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16437).
Definition t256_4_6 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16438).

(* Signature *)
Definition tyin_A128____dumpstate_avx2 : seq atype :=
  [:: aarr U8 128; aword U64; aint; aarr U256 7 ].
Definition args_A128____dumpstate_avx2 : seq var_i :=
  [:: buf_92.(gv); offset_87.(gv); _LEN_55.(gv); st_62.(gv) ].
Definition tyout_A128____dumpstate_avx2 : seq atype :=
  [:: aarr U8 128; aword U64 ].
Definition res_A128____dumpstate_avx2 : seq var_i :=
  [:: buf_92.(gv); offset_87.(gv) ].

(* Body *)
Definition body_A128____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_60.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_55))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_92.(gv)
                                                                ; Lvar DELTA_60.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A128____a_ilen_write_upto32 [:: Pvar buf_92
                                                                    ; Pvar offset_87
                                                                    ; Pvar DELTA_60
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_62 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_55.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_55) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_92.(gv)
                                                                ; Lvar DELTA_60.(gv)
                                                                ; Lvar _LEN_55.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_92
                                                                    ; Pvar offset_87
                                                                    ; Pvar DELTA_60
                                                                    ; Pvar _LEN_55
                                                                    ; Pget Aligned AAscale U256 st_62 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_92.(gv)
                                    ; Lvar DELTA_60.(gv)
                                    ; Lvar _LEN_55.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_92
                                                                    ; Pvar offset_87
                                                                    ; Pvar DELTA_60
                                                                    ; Pvar _LEN_55
                                                                    ; Pget Aligned AAscale U256 st_62 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_55))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_14.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_62 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_21.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_62 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_8.(gv)) AT_none (aword U64) (Pvar t128_1_21))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_92.(gv)
                                                                ; Lvar DELTA_60.(gv)
                                                                ; Lvar _LEN_55.(gv) ] A128____a_ilen_write_upto8 [:: Pvar buf_92
                                                                    ; Pvar offset_87
                                                                    ; Pvar DELTA_60
                                                                    ; Pvar _LEN_55
                                                                    ; Pvar t_8 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_21.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_21
                                                                    ; Pvar t128_1_21 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_55))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_62 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_62 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_62 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_62 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_62 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_62 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_62 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_62 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_9
                                                                    ; Pvar t256_3_7
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_92.(gv)
                                                                  ; Lvar DELTA_60.(gv)
                                                                  ; Lvar _LEN_55.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_92
                                                                    ; Pvar offset_87
                                                                    ; Pvar DELTA_60
                                                                    ; Pvar _LEN_55
                                                                    ; Pvar t256_4_6 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_55))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_8.(gv)) AT_none (aword U64) (Pvar t128_0_14))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_92.(gv)
                                                                    ; Lvar DELTA_60.(gv)
                                                                    ; Lvar _LEN_55.(gv) ] A128____a_ilen_write_upto8 [:: Pvar buf_92
                                                                    ; Pvar offset_87
                                                                    ; Pvar DELTA_60
                                                                    ; Pvar _LEN_55
                                                                    ; Pvar t_8 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_14
                                                                    ; Pvar t128_0_14 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_55))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_7
                                                                    ; Pvar t256_1_9
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_92.(gv)
                                                                    ; Lvar DELTA_60.(gv)
                                                                    ; Lvar _LEN_55.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_92
                                                                    ; Pvar offset_87
                                                                    ; Pvar DELTA_60
                                                                    ; Pvar _LEN_55
                                                                    ; Pvar t256_4_6 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_55))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_8.(gv)) AT_none (aword U64) (Pvar t128_1_21))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_92.(gv)
                                                                    ; Lvar DELTA_60.(gv)
                                                                    ; Lvar _LEN_55.(gv) ] A128____a_ilen_write_upto8 [:: Pvar buf_92
                                                                    ; Pvar offset_87
                                                                    ; Pvar DELTA_60
                                                                    ; Pvar _LEN_55
                                                                    ; Pvar t_8 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_55))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_9
                                                                    ; Pvar t256_0_9
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_92.(gv)
                                                                    ; Lvar DELTA_60.(gv)
                                                                    ; Lvar _LEN_55.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_92
                                                                    ; Pvar offset_87
                                                                    ; Pvar DELTA_60
                                                                    ; Pvar _LEN_55
                                                                    ; Pvar t256_4_6 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_55))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_8.(gv)) AT_none (aword U64) (Pvar t128_0_14))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_92.(gv)
                                                                    ; Lvar DELTA_60.(gv)
                                                                    ; Lvar _LEN_55.(gv) ] A128____a_ilen_write_upto8 [:: Pvar buf_92
                                                                    ; Pvar offset_87
                                                                    ; Pvar DELTA_60
                                                                    ; Pvar _LEN_55
                                                                    ; Pvar t_8 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_55))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_9
                                                                    ; Pvar t256_2_9
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_92.(gv)
                                                                    ; Lvar DELTA_60.(gv)
                                                                    ; Lvar _LEN_55.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_92
                                                                    ; Pvar offset_87
                                                                    ; Pvar DELTA_60
                                                                    ; Pvar _LEN_55
                                                                    ; Pvar t256_4_6 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_87.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_87) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_60)))) ].

Definition fd_A128____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____dumpstate_avx2;
    f_params := args_A128____dumpstate_avx2;
    f_body := body_A128____dumpstate_avx2;
    f_tyout := tyout_A128____dumpstate_avx2;
    f_res := res_A128____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
