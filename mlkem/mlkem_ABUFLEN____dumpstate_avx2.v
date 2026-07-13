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

(* ABUFLEN____dumpstate_avx2 *)
(* Local variables *)
Definition buf_162 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14516).
Definition offset_172 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14517).
Definition _LEN_105 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14518).
Definition st_112 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14519).
Definition DELTA_115 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14520).
Definition t128_0_24 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14521).
Definition t128_1_36 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14522).
Definition t_13 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14523).
Definition t256_0_14 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14524).
Definition t256_1_14 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14525).
Definition t256_2_14 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14526).
Definition t256_3_12 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14527).
Definition t256_4_11 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14528).

(* Signature *)
Definition tyin_ABUFLEN____dumpstate_avx2 : seq atype :=
  [:: aarr U8 536; aword U64; aint; aarr U256 7 ].
Definition args_ABUFLEN____dumpstate_avx2 : seq var_i :=
  [:: buf_162.(gv); offset_172.(gv); _LEN_105.(gv); st_112.(gv) ].
Definition tyout_ABUFLEN____dumpstate_avx2 : seq atype :=
  [:: aarr U8 536; aword U64 ].
Definition res_ABUFLEN____dumpstate_avx2 : seq var_i :=
  [:: buf_162.(gv); offset_172.(gv) ].

(* Body *)
Definition body_ABUFLEN____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_115.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_105))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_162.(gv)
                                                                ; Lvar DELTA_115.(gv)
                                                                ; Lnone dummy_var_info (aint) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_162
                                                                    ; Pvar offset_172
                                                                    ; Pvar DELTA_115
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_112 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_105.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_105) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_162.(gv)
                                                                ; Lvar DELTA_115.(gv)
                                                                ; Lvar _LEN_105.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_162
                                                                    ; Pvar offset_172
                                                                    ; Pvar DELTA_115
                                                                    ; Pvar _LEN_105
                                                                    ; Pget Aligned AAscale U256 st_112 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_162.(gv)
                                    ; Lvar DELTA_115.(gv)
                                    ; Lvar _LEN_105.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_162
                                                                    ; Pvar offset_172
                                                                    ; Pvar DELTA_115
                                                                    ; Pvar _LEN_105
                                                                    ; Pget Aligned AAscale U256 st_112 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_105))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_24.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_112 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_36.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_112 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_13.(gv)) AT_none (aword U64) (Pvar t128_1_36))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_162.(gv)
                                                                ; Lvar DELTA_115.(gv)
                                                                ; Lvar _LEN_105.(gv) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf_162
                                                                    ; Pvar offset_172
                                                                    ; Pvar DELTA_115
                                                                    ; Pvar _LEN_105
                                                                    ; Pvar t_13 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_36.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_36
                                                                    ; Pvar t128_1_36 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_105))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_112 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_112 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_112 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_112 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_112 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_112 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_12.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_112 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_112 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_14
                                                                    ; Pvar t256_3_12
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_162.(gv)
                                                                  ; Lvar DELTA_115.(gv)
                                                                  ; Lvar _LEN_105.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_162
                                                                    ; Pvar offset_172
                                                                    ; Pvar DELTA_115
                                                                    ; Pvar _LEN_105
                                                                    ; Pvar t256_4_11 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_105))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_13.(gv)) AT_none (aword U64) (Pvar t128_0_24))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_162.(gv)
                                                                    ; Lvar DELTA_115.(gv)
                                                                    ; Lvar _LEN_105.(gv) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf_162
                                                                    ; Pvar offset_172
                                                                    ; Pvar DELTA_115
                                                                    ; Pvar _LEN_105
                                                                    ; Pvar t_13 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_24.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_24
                                                                    ; Pvar t128_0_24 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_105))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_12
                                                                    ; Pvar t256_1_14
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_162.(gv)
                                                                    ; Lvar DELTA_115.(gv)
                                                                    ; Lvar _LEN_105.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_162
                                                                    ; Pvar offset_172
                                                                    ; Pvar DELTA_115
                                                                    ; Pvar _LEN_105
                                                                    ; Pvar t256_4_11 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_105))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_13.(gv)) AT_none (aword U64) (Pvar t128_1_36))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_162.(gv)
                                                                    ; Lvar DELTA_115.(gv)
                                                                    ; Lvar _LEN_105.(gv) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf_162
                                                                    ; Pvar offset_172
                                                                    ; Pvar DELTA_115
                                                                    ; Pvar _LEN_105
                                                                    ; Pvar t_13 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_105))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_14
                                                                    ; Pvar t256_0_14
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_162.(gv)
                                                                    ; Lvar DELTA_115.(gv)
                                                                    ; Lvar _LEN_105.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_162
                                                                    ; Pvar offset_172
                                                                    ; Pvar DELTA_115
                                                                    ; Pvar _LEN_105
                                                                    ; Pvar t256_4_11 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_105))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_13.(gv)) AT_none (aword U64) (Pvar t128_0_24))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_162.(gv)
                                                                    ; Lvar DELTA_115.(gv)
                                                                    ; Lvar _LEN_105.(gv) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf_162
                                                                    ; Pvar offset_172
                                                                    ; Pvar DELTA_115
                                                                    ; Pvar _LEN_105
                                                                    ; Pvar t_13 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_105))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_14
                                                                    ; Pvar t256_2_14
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_162.(gv)
                                                                    ; Lvar DELTA_115.(gv)
                                                                    ; Lvar _LEN_105.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_162
                                                                    ; Pvar offset_172
                                                                    ; Pvar DELTA_115
                                                                    ; Pvar _LEN_105
                                                                    ; Pvar t256_4_11 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_172.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_172) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_115)))) ].

Definition fd_ABUFLEN____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____dumpstate_avx2;
    f_params := args_ABUFLEN____dumpstate_avx2;
    f_body := body_ABUFLEN____dumpstate_avx2;
    f_tyout := tyout_ABUFLEN____dumpstate_avx2;
    f_res := res_ABUFLEN____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
