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

(* A1184____dumpstate_avx2 *)
(* Local variables *)
Definition buf_106 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16044).
Definition offset_104 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16045).
Definition _LEN_65 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16046).
Definition st_72 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16047).
Definition DELTA_71 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16048).
Definition t128_0_16 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16049).
Definition t128_1_24 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16050).
Definition t_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16051).
Definition t256_0_10 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16052).
Definition t256_1_10 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16053).
Definition t256_2_10 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16054).
Definition t256_3_8 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16055).
Definition t256_4_7 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16056).

(* Signature *)
Definition tyin_A1184____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1184; aword U64; aint; aarr U256 7 ].
Definition args_A1184____dumpstate_avx2 : seq var_i :=
  [:: buf_106.(gv); offset_104.(gv); _LEN_65.(gv); st_72.(gv) ].
Definition tyout_A1184____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1184; aword U64 ].
Definition res_A1184____dumpstate_avx2 : seq var_i :=
  [:: buf_106.(gv); offset_104.(gv) ].

(* Body *)
Definition body_A1184____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_71.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_65))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_106.(gv)
                                                                ; Lvar DELTA_71.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A1184____a_ilen_write_upto32 [:: Pvar buf_106
                                                                    ; Pvar offset_104
                                                                    ; Pvar DELTA_71
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_72 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_65.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_65) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_106.(gv)
                                                                ; Lvar DELTA_71.(gv)
                                                                ; Lvar _LEN_65.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_106
                                                                    ; Pvar offset_104
                                                                    ; Pvar DELTA_71
                                                                    ; Pvar _LEN_65
                                                                    ; Pget Aligned AAscale U256 st_72 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_106.(gv)
                                    ; Lvar DELTA_71.(gv)
                                    ; Lvar _LEN_65.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_106
                                                                    ; Pvar offset_104
                                                                    ; Pvar DELTA_71
                                                                    ; Pvar _LEN_65
                                                                    ; Pget Aligned AAscale U256 st_72 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_65))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_16.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_72 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_24.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_72 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_9.(gv)) AT_none (aword U64) (Pvar t128_1_24))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_106.(gv)
                                                                ; Lvar DELTA_71.(gv)
                                                                ; Lvar _LEN_65.(gv) ] A1184____a_ilen_write_upto8 [:: Pvar buf_106
                                                                    ; Pvar offset_104
                                                                    ; Pvar DELTA_71
                                                                    ; Pvar _LEN_65
                                                                    ; Pvar t_9 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_24.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_24
                                                                    ; Pvar t128_1_24 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_65))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_72 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_72 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_72 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_72 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_72 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_72 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_72 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_72 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_10
                                                                    ; Pvar t256_3_8
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_106.(gv)
                                                                  ; Lvar DELTA_71.(gv)
                                                                  ; Lvar _LEN_65.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_106
                                                                    ; Pvar offset_104
                                                                    ; Pvar DELTA_71
                                                                    ; Pvar _LEN_65
                                                                    ; Pvar t256_4_7 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_65))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_9.(gv)) AT_none (aword U64) (Pvar t128_0_16))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_106.(gv)
                                                                    ; Lvar DELTA_71.(gv)
                                                                    ; Lvar _LEN_65.(gv) ] A1184____a_ilen_write_upto8 [:: Pvar buf_106
                                                                    ; Pvar offset_104
                                                                    ; Pvar DELTA_71
                                                                    ; Pvar _LEN_65
                                                                    ; Pvar t_9 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_16.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_16
                                                                    ; Pvar t128_0_16 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_65))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_8
                                                                    ; Pvar t256_1_10
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_106.(gv)
                                                                    ; Lvar DELTA_71.(gv)
                                                                    ; Lvar _LEN_65.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_106
                                                                    ; Pvar offset_104
                                                                    ; Pvar DELTA_71
                                                                    ; Pvar _LEN_65
                                                                    ; Pvar t256_4_7 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_65))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_9.(gv)) AT_none (aword U64) (Pvar t128_1_24))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_106.(gv)
                                                                    ; Lvar DELTA_71.(gv)
                                                                    ; Lvar _LEN_65.(gv) ] A1184____a_ilen_write_upto8 [:: Pvar buf_106
                                                                    ; Pvar offset_104
                                                                    ; Pvar DELTA_71
                                                                    ; Pvar _LEN_65
                                                                    ; Pvar t_9 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_65))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_10
                                                                    ; Pvar t256_0_10
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_106.(gv)
                                                                    ; Lvar DELTA_71.(gv)
                                                                    ; Lvar _LEN_65.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_106
                                                                    ; Pvar offset_104
                                                                    ; Pvar DELTA_71
                                                                    ; Pvar _LEN_65
                                                                    ; Pvar t256_4_7 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_65))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_9.(gv)) AT_none (aword U64) (Pvar t128_0_16))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_106.(gv)
                                                                    ; Lvar DELTA_71.(gv)
                                                                    ; Lvar _LEN_65.(gv) ] A1184____a_ilen_write_upto8 [:: Pvar buf_106
                                                                    ; Pvar offset_104
                                                                    ; Pvar DELTA_71
                                                                    ; Pvar _LEN_65
                                                                    ; Pvar t_9 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_65))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_10
                                                                    ; Pvar t256_2_10
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_106.(gv)
                                                                    ; Lvar DELTA_71.(gv)
                                                                    ; Lvar _LEN_65.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_106
                                                                    ; Pvar offset_104
                                                                    ; Pvar DELTA_71
                                                                    ; Pvar _LEN_65
                                                                    ; Pvar t256_4_7 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_104.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_104) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_71)))) ].

Definition fd_A1184____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____dumpstate_avx2;
    f_params := args_A1184____dumpstate_avx2;
    f_body := body_A1184____dumpstate_avx2;
    f_tyout := tyout_A1184____dumpstate_avx2;
    f_res := res_A1184____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
