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

(* A1600____dumpstate_avx2 *)
(* Local variables *)
Definition buf_148 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14898).
Definition offset_155 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14899).
Definition _LEN_95 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14900).
Definition st_102 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14901).
Definition DELTA_104 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14902).
Definition t128_0_22 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14903).
Definition t128_1_33 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14904).
Definition t_12 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14905).
Definition t256_0_13 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14906).
Definition t256_1_13 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14907).
Definition t256_2_13 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14908).
Definition t256_3_11 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14909).
Definition t256_4_10 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14910).

(* Signature *)
Definition tyin_A1600____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1600; aword U64; aint; aarr U256 7 ].
Definition args_A1600____dumpstate_avx2 : seq var_i :=
  [:: buf_148.(gv); offset_155.(gv); _LEN_95.(gv); st_102.(gv) ].
Definition tyout_A1600____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1600; aword U64 ].
Definition res_A1600____dumpstate_avx2 : seq var_i :=
  [:: buf_148.(gv); offset_155.(gv) ].

(* Body *)
Definition body_A1600____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_104.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_95))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_148.(gv)
                                                                ; Lvar DELTA_104.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A1600____a_ilen_write_upto32 [:: Pvar buf_148
                                                                    ; Pvar offset_155
                                                                    ; Pvar DELTA_104
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_102 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_95.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_95) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_148.(gv)
                                                                ; Lvar DELTA_104.(gv)
                                                                ; Lvar _LEN_95.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_148
                                                                    ; Pvar offset_155
                                                                    ; Pvar DELTA_104
                                                                    ; Pvar _LEN_95
                                                                    ; Pget Aligned AAscale U256 st_102 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_148.(gv)
                                    ; Lvar DELTA_104.(gv)
                                    ; Lvar _LEN_95.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_148
                                                                    ; Pvar offset_155
                                                                    ; Pvar DELTA_104
                                                                    ; Pvar _LEN_95
                                                                    ; Pget Aligned AAscale U256 st_102 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_95))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_22.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_102 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_33.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_102 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_12.(gv)) AT_none (aword U64) (Pvar t128_1_33))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_148.(gv)
                                                                ; Lvar DELTA_104.(gv)
                                                                ; Lvar _LEN_95.(gv) ] A1600____a_ilen_write_upto8 [:: Pvar buf_148
                                                                    ; Pvar offset_155
                                                                    ; Pvar DELTA_104
                                                                    ; Pvar _LEN_95
                                                                    ; Pvar t_12 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_33.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_33
                                                                    ; Pvar t128_1_33 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_95))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_13.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_102 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_102 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_13.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_102 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_102 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_13.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_102 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_102 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_102 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_102 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_13
                                                                    ; Pvar t256_3_11
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_148.(gv)
                                                                  ; Lvar DELTA_104.(gv)
                                                                  ; Lvar _LEN_95.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_148
                                                                    ; Pvar offset_155
                                                                    ; Pvar DELTA_104
                                                                    ; Pvar _LEN_95
                                                                    ; Pvar t256_4_10 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_95))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_12.(gv)) AT_none (aword U64) (Pvar t128_0_22))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_148.(gv)
                                                                    ; Lvar DELTA_104.(gv)
                                                                    ; Lvar _LEN_95.(gv) ] A1600____a_ilen_write_upto8 [:: Pvar buf_148
                                                                    ; Pvar offset_155
                                                                    ; Pvar DELTA_104
                                                                    ; Pvar _LEN_95
                                                                    ; Pvar t_12 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_22.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_22
                                                                    ; Pvar t128_0_22 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_95))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_11
                                                                    ; Pvar t256_1_13
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_148.(gv)
                                                                    ; Lvar DELTA_104.(gv)
                                                                    ; Lvar _LEN_95.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_148
                                                                    ; Pvar offset_155
                                                                    ; Pvar DELTA_104
                                                                    ; Pvar _LEN_95
                                                                    ; Pvar t256_4_10 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_95))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_12.(gv)) AT_none (aword U64) (Pvar t128_1_33))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_148.(gv)
                                                                    ; Lvar DELTA_104.(gv)
                                                                    ; Lvar _LEN_95.(gv) ] A1600____a_ilen_write_upto8 [:: Pvar buf_148
                                                                    ; Pvar offset_155
                                                                    ; Pvar DELTA_104
                                                                    ; Pvar _LEN_95
                                                                    ; Pvar t_12 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_95))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_13
                                                                    ; Pvar t256_0_13
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_148.(gv)
                                                                    ; Lvar DELTA_104.(gv)
                                                                    ; Lvar _LEN_95.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_148
                                                                    ; Pvar offset_155
                                                                    ; Pvar DELTA_104
                                                                    ; Pvar _LEN_95
                                                                    ; Pvar t256_4_10 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_95))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_12.(gv)) AT_none (aword U64) (Pvar t128_0_22))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_148.(gv)
                                                                    ; Lvar DELTA_104.(gv)
                                                                    ; Lvar _LEN_95.(gv) ] A1600____a_ilen_write_upto8 [:: Pvar buf_148
                                                                    ; Pvar offset_155
                                                                    ; Pvar DELTA_104
                                                                    ; Pvar _LEN_95
                                                                    ; Pvar t_12 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_95))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_13
                                                                    ; Pvar t256_2_13
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_148.(gv)
                                                                    ; Lvar DELTA_104.(gv)
                                                                    ; Lvar _LEN_95.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_148
                                                                    ; Pvar offset_155
                                                                    ; Pvar DELTA_104
                                                                    ; Pvar _LEN_95
                                                                    ; Pvar t256_4_10 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_155.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_155) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_104)))) ].

Definition fd_A1600____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____dumpstate_avx2;
    f_params := args_A1600____dumpstate_avx2;
    f_body := body_A1600____dumpstate_avx2;
    f_tyout := tyout_A1600____dumpstate_avx2;
    f_res := res_A1600____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
