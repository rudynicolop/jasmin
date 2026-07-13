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

(* A64____dumpstate_avx2 *)
(* Local variables *)
Definition buf_80 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16673).
Definition offset_76 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16674).
Definition _LEN_51 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16675).
Definition st_58 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16676).
Definition DELTA_51 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16677).
Definition t128_0_12 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16678).
Definition t128_1_18 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16679).
Definition t_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16680).
Definition t256_0_8 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16681).
Definition t256_1_8 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16682).
Definition t256_2_8 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16683).
Definition t256_3_6 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16684).
Definition t256_4_5 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16685).

(* Signature *)
Definition tyin_A64____dumpstate_avx2 : seq atype :=
  [:: aarr U8 64; aword U64; aint; aarr U256 7 ].
Definition args_A64____dumpstate_avx2 : seq var_i :=
  [:: buf_80.(gv); offset_76.(gv); _LEN_51.(gv); st_58.(gv) ].
Definition tyout_A64____dumpstate_avx2 : seq atype :=
  [:: aarr U8 64; aword U64 ].
Definition res_A64____dumpstate_avx2 : seq var_i :=
  [:: buf_80.(gv); offset_76.(gv) ].

(* Body *)
Definition body_A64____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_51.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_51))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_80.(gv)
                                                                ; Lvar DELTA_51.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A64____a_ilen_write_upto32 [:: Pvar buf_80
                                                                    ; Pvar offset_76
                                                                    ; Pvar DELTA_51
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_58 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_51.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_51) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_80.(gv)
                                                                ; Lvar DELTA_51.(gv)
                                                                ; Lvar _LEN_51.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_80
                                                                    ; Pvar offset_76
                                                                    ; Pvar DELTA_51
                                                                    ; Pvar _LEN_51
                                                                    ; Pget Aligned AAscale U256 st_58 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_80.(gv)
                                    ; Lvar DELTA_51.(gv)
                                    ; Lvar _LEN_51.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_80
                                                                    ; Pvar offset_76
                                                                    ; Pvar DELTA_51
                                                                    ; Pvar _LEN_51
                                                                    ; Pget Aligned AAscale U256 st_58 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_51))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_12.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_58 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_18.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_58 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_7.(gv)) AT_none (aword U64) (Pvar t128_1_18))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_80.(gv)
                                                                ; Lvar DELTA_51.(gv)
                                                                ; Lvar _LEN_51.(gv) ] A64____a_ilen_write_upto8 [:: Pvar buf_80
                                                                    ; Pvar offset_76
                                                                    ; Pvar DELTA_51
                                                                    ; Pvar _LEN_51
                                                                    ; Pvar t_7 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_18.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_18
                                                                    ; Pvar t128_1_18 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_51))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_58 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_58 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_58 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_58 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_58 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_58 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_58 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_58 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_8
                                                                    ; Pvar t256_3_6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_80.(gv)
                                                                  ; Lvar DELTA_51.(gv)
                                                                  ; Lvar _LEN_51.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_80
                                                                    ; Pvar offset_76
                                                                    ; Pvar DELTA_51
                                                                    ; Pvar _LEN_51
                                                                    ; Pvar t256_4_5 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_51))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_7.(gv)) AT_none (aword U64) (Pvar t128_0_12))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_80.(gv)
                                                                    ; Lvar DELTA_51.(gv)
                                                                    ; Lvar _LEN_51.(gv) ] A64____a_ilen_write_upto8 [:: Pvar buf_80
                                                                    ; Pvar offset_76
                                                                    ; Pvar DELTA_51
                                                                    ; Pvar _LEN_51
                                                                    ; Pvar t_7 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_12.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_12
                                                                    ; Pvar t128_0_12 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_51))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_6
                                                                    ; Pvar t256_1_8
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_80.(gv)
                                                                    ; Lvar DELTA_51.(gv)
                                                                    ; Lvar _LEN_51.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_80
                                                                    ; Pvar offset_76
                                                                    ; Pvar DELTA_51
                                                                    ; Pvar _LEN_51
                                                                    ; Pvar t256_4_5 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_51))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_7.(gv)) AT_none (aword U64) (Pvar t128_1_18))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_80.(gv)
                                                                    ; Lvar DELTA_51.(gv)
                                                                    ; Lvar _LEN_51.(gv) ] A64____a_ilen_write_upto8 [:: Pvar buf_80
                                                                    ; Pvar offset_76
                                                                    ; Pvar DELTA_51
                                                                    ; Pvar _LEN_51
                                                                    ; Pvar t_7 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_51))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_8
                                                                    ; Pvar t256_0_8
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_80.(gv)
                                                                    ; Lvar DELTA_51.(gv)
                                                                    ; Lvar _LEN_51.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_80
                                                                    ; Pvar offset_76
                                                                    ; Pvar DELTA_51
                                                                    ; Pvar _LEN_51
                                                                    ; Pvar t256_4_5 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_51))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_7.(gv)) AT_none (aword U64) (Pvar t128_0_12))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_80.(gv)
                                                                    ; Lvar DELTA_51.(gv)
                                                                    ; Lvar _LEN_51.(gv) ] A64____a_ilen_write_upto8 [:: Pvar buf_80
                                                                    ; Pvar offset_76
                                                                    ; Pvar DELTA_51
                                                                    ; Pvar _LEN_51
                                                                    ; Pvar t_7 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_51))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_8
                                                                    ; Pvar t256_2_8
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_80.(gv)
                                                                    ; Lvar DELTA_51.(gv)
                                                                    ; Lvar _LEN_51.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_80
                                                                    ; Pvar offset_76
                                                                    ; Pvar DELTA_51
                                                                    ; Pvar _LEN_51
                                                                    ; Pvar t256_4_5 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_76.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_76) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_51)))) ].

Definition fd_A64____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____dumpstate_avx2;
    f_params := args_A64____dumpstate_avx2;
    f_body := body_A64____dumpstate_avx2;
    f_tyout := tyout_A64____dumpstate_avx2;
    f_res := res_A64____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
