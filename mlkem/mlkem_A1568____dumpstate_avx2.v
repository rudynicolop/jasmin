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

(* A1568____dumpstate_avx2 *)
(* Local variables *)
Definition buf_120 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15662).
Definition offset_121 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15663).
Definition _LEN_75 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15664).
Definition st_82 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 15665).
Definition DELTA_82 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15666).
Definition t128_0_18 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15667).
Definition t128_1_27 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15668).
Definition t_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15669).
Definition t256_0_11 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15670).
Definition t256_1_11 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15671).
Definition t256_2_11 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15672).
Definition t256_3_9 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15673).
Definition t256_4_8 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15674).

(* Signature *)
Definition tyin_A1568____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aarr U256 7 ].
Definition args_A1568____dumpstate_avx2 : seq var_i :=
  [:: buf_120.(gv); offset_121.(gv); _LEN_75.(gv); st_82.(gv) ].
Definition tyout_A1568____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1568; aword U64 ].
Definition res_A1568____dumpstate_avx2 : seq var_i :=
  [:: buf_120.(gv); offset_121.(gv) ].

(* Body *)
Definition body_A1568____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_82.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_75))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_120.(gv)
                                                                ; Lvar DELTA_82.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A1568____a_ilen_write_upto32 [:: Pvar buf_120
                                                                    ; Pvar offset_121
                                                                    ; Pvar DELTA_82
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_82 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_75.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_75) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_120.(gv)
                                                                ; Lvar DELTA_82.(gv)
                                                                ; Lvar _LEN_75.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_120
                                                                    ; Pvar offset_121
                                                                    ; Pvar DELTA_82
                                                                    ; Pvar _LEN_75
                                                                    ; Pget Aligned AAscale U256 st_82 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_120.(gv)
                                    ; Lvar DELTA_82.(gv)
                                    ; Lvar _LEN_75.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_120
                                                                    ; Pvar offset_121
                                                                    ; Pvar DELTA_82
                                                                    ; Pvar _LEN_75
                                                                    ; Pget Aligned AAscale U256 st_82 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_75))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_18.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_82 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_27.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_82 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_10.(gv)) AT_none (aword U64) (Pvar t128_1_27))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_120.(gv)
                                                                ; Lvar DELTA_82.(gv)
                                                                ; Lvar _LEN_75.(gv) ] A1568____a_ilen_write_upto8 [:: Pvar buf_120
                                                                    ; Pvar offset_121
                                                                    ; Pvar DELTA_82
                                                                    ; Pvar _LEN_75
                                                                    ; Pvar t_10 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_27.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_27
                                                                    ; Pvar t128_1_27 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_75))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_82 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_82 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_82 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_82 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_82 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_82 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_82 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_82 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_11
                                                                    ; Pvar t256_3_9
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_120.(gv)
                                                                  ; Lvar DELTA_82.(gv)
                                                                  ; Lvar _LEN_75.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_120
                                                                    ; Pvar offset_121
                                                                    ; Pvar DELTA_82
                                                                    ; Pvar _LEN_75
                                                                    ; Pvar t256_4_8 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_75))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_10.(gv)) AT_none (aword U64) (Pvar t128_0_18))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_120.(gv)
                                                                    ; Lvar DELTA_82.(gv)
                                                                    ; Lvar _LEN_75.(gv) ] A1568____a_ilen_write_upto8 [:: Pvar buf_120
                                                                    ; Pvar offset_121
                                                                    ; Pvar DELTA_82
                                                                    ; Pvar _LEN_75
                                                                    ; Pvar t_10 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_18.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_18
                                                                    ; Pvar t128_0_18 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_75))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_9
                                                                    ; Pvar t256_1_11
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_120.(gv)
                                                                    ; Lvar DELTA_82.(gv)
                                                                    ; Lvar _LEN_75.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_120
                                                                    ; Pvar offset_121
                                                                    ; Pvar DELTA_82
                                                                    ; Pvar _LEN_75
                                                                    ; Pvar t256_4_8 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_75))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_10.(gv)) AT_none (aword U64) (Pvar t128_1_27))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_120.(gv)
                                                                    ; Lvar DELTA_82.(gv)
                                                                    ; Lvar _LEN_75.(gv) ] A1568____a_ilen_write_upto8 [:: Pvar buf_120
                                                                    ; Pvar offset_121
                                                                    ; Pvar DELTA_82
                                                                    ; Pvar _LEN_75
                                                                    ; Pvar t_10 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_75))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_11
                                                                    ; Pvar t256_0_11
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_120.(gv)
                                                                    ; Lvar DELTA_82.(gv)
                                                                    ; Lvar _LEN_75.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_120
                                                                    ; Pvar offset_121
                                                                    ; Pvar DELTA_82
                                                                    ; Pvar _LEN_75
                                                                    ; Pvar t256_4_8 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_75))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_10.(gv)) AT_none (aword U64) (Pvar t128_0_18))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_120.(gv)
                                                                    ; Lvar DELTA_82.(gv)
                                                                    ; Lvar _LEN_75.(gv) ] A1568____a_ilen_write_upto8 [:: Pvar buf_120
                                                                    ; Pvar offset_121
                                                                    ; Pvar DELTA_82
                                                                    ; Pvar _LEN_75
                                                                    ; Pvar t_10 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_75))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_11
                                                                    ; Pvar t256_2_11
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_120.(gv)
                                                                    ; Lvar DELTA_82.(gv)
                                                                    ; Lvar _LEN_75.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_120
                                                                    ; Pvar offset_121
                                                                    ; Pvar DELTA_82
                                                                    ; Pvar _LEN_75
                                                                    ; Pvar t256_4_8 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_121.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_121) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_82)))) ].

Definition fd_A1568____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____dumpstate_avx2;
    f_params := args_A1568____dumpstate_avx2;
    f_body := body_A1568____dumpstate_avx2;
    f_tyout := tyout_A1568____dumpstate_avx2;
    f_res := res_A1568____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
