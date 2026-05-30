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

(* A32____dumpstate_avx2 *)
(* Local variables *)
Definition buf_52 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17437).
Definition offset_42 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17438).
Definition _LEN_31 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17439).
Definition st_38 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 17440).
Definition DELTA_29 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17441).
Definition t128_0_8 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17442).
Definition t128_1_12 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17443).
Definition t_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17444).
Definition t256_0_6 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17445).
Definition t256_1_6 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17446).
Definition t256_2_6 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17447).
Definition t256_3_4 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17448).
Definition t256_4_3 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17449).

(* Signature *)
Definition tyin_A32____dumpstate_avx2 : seq atype :=
  [:: aarr U8 32; aword U64; aint; aarr U256 7 ].
Definition args_A32____dumpstate_avx2 : seq var_i :=
  [:: buf_52.(gv); offset_42.(gv); _LEN_31.(gv); st_38.(gv) ].
Definition tyout_A32____dumpstate_avx2 : seq atype :=
  [:: aarr U8 32; aword U64 ].
Definition res_A32____dumpstate_avx2 : seq var_i :=
  [:: buf_52.(gv); offset_42.(gv) ].

(* Body *)
Definition body_A32____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_29.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_31))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_52.(gv)
                                                                ; Lvar DELTA_29.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A32____a_ilen_write_upto32 [:: Pvar buf_52
                                                                    ; Pvar offset_42
                                                                    ; Pvar DELTA_29
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_38 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_31.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_31) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_52.(gv)
                                                                ; Lvar DELTA_29.(gv)
                                                                ; Lvar _LEN_31.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_52
                                                                    ; Pvar offset_42
                                                                    ; Pvar DELTA_29
                                                                    ; Pvar _LEN_31
                                                                    ; Pget Aligned AAscale U256 st_38 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_52.(gv)
                                    ; Lvar DELTA_29.(gv)
                                    ; Lvar _LEN_31.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_52
                                                                    ; Pvar offset_42
                                                                    ; Pvar DELTA_29
                                                                    ; Pvar _LEN_31
                                                                    ; Pget Aligned AAscale U256 st_38 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_31))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_8.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_38 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_12.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_38 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_5.(gv)) AT_none (aword U64) (Pvar t128_1_12))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_52.(gv)
                                                                ; Lvar DELTA_29.(gv)
                                                                ; Lvar _LEN_31.(gv) ] A32____a_ilen_write_upto8 [:: Pvar buf_52
                                                                    ; Pvar offset_42
                                                                    ; Pvar DELTA_29
                                                                    ; Pvar _LEN_31
                                                                    ; Pvar t_5 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_12.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_12
                                                                    ; Pvar t128_1_12 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_31))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_38 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_38 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_38 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_38 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_38 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_38 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_38 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_38 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_6
                                                                    ; Pvar t256_3_4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_52.(gv)
                                                                  ; Lvar DELTA_29.(gv)
                                                                  ; Lvar _LEN_31.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_52
                                                                    ; Pvar offset_42
                                                                    ; Pvar DELTA_29
                                                                    ; Pvar _LEN_31
                                                                    ; Pvar t256_4_3 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_31))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_5.(gv)) AT_none (aword U64) (Pvar t128_0_8))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_52.(gv)
                                                                    ; Lvar DELTA_29.(gv)
                                                                    ; Lvar _LEN_31.(gv) ] A32____a_ilen_write_upto8 [:: Pvar buf_52
                                                                    ; Pvar offset_42
                                                                    ; Pvar DELTA_29
                                                                    ; Pvar _LEN_31
                                                                    ; Pvar t_5 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_8
                                                                    ; Pvar t128_0_8 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_31))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_4
                                                                    ; Pvar t256_1_6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_52.(gv)
                                                                    ; Lvar DELTA_29.(gv)
                                                                    ; Lvar _LEN_31.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_52
                                                                    ; Pvar offset_42
                                                                    ; Pvar DELTA_29
                                                                    ; Pvar _LEN_31
                                                                    ; Pvar t256_4_3 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_31))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_5.(gv)) AT_none (aword U64) (Pvar t128_1_12))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_52.(gv)
                                                                    ; Lvar DELTA_29.(gv)
                                                                    ; Lvar _LEN_31.(gv) ] A32____a_ilen_write_upto8 [:: Pvar buf_52
                                                                    ; Pvar offset_42
                                                                    ; Pvar DELTA_29
                                                                    ; Pvar _LEN_31
                                                                    ; Pvar t_5 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_31))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_6
                                                                    ; Pvar t256_0_6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_52.(gv)
                                                                    ; Lvar DELTA_29.(gv)
                                                                    ; Lvar _LEN_31.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_52
                                                                    ; Pvar offset_42
                                                                    ; Pvar DELTA_29
                                                                    ; Pvar _LEN_31
                                                                    ; Pvar t256_4_3 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_31))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_5.(gv)) AT_none (aword U64) (Pvar t128_0_8))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_52.(gv)
                                                                    ; Lvar DELTA_29.(gv)
                                                                    ; Lvar _LEN_31.(gv) ] A32____a_ilen_write_upto8 [:: Pvar buf_52
                                                                    ; Pvar offset_42
                                                                    ; Pvar DELTA_29
                                                                    ; Pvar _LEN_31
                                                                    ; Pvar t_5 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_31))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_6
                                                                    ; Pvar t256_2_6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_52.(gv)
                                                                    ; Lvar DELTA_29.(gv)
                                                                    ; Lvar _LEN_31.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_52
                                                                    ; Pvar offset_42
                                                                    ; Pvar DELTA_29
                                                                    ; Pvar _LEN_31
                                                                    ; Pvar t256_4_3 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_42.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_42) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_29)))) ].

Definition fd_A32____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____dumpstate_avx2;
    f_params := args_A32____dumpstate_avx2;
    f_body := body_A32____dumpstate_avx2;
    f_tyout := tyout_A32____dumpstate_avx2;
    f_res := res_A32____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
