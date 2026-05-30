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

(* A33____dumpstate_avx2 *)
(* Local variables *)
Definition buf_66 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17055).
Definition offset_59 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17056).
Definition _LEN_41 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17057).
Definition st_48 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 17058).
Definition DELTA_40 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17059).
Definition t128_0_10 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17060).
Definition t128_1_15 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17061).
Definition t_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17062).
Definition t256_0_7 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17063).
Definition t256_1_7 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17064).
Definition t256_2_7 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17065).
Definition t256_3_5 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17066).
Definition t256_4_4 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17067).

(* Signature *)
Definition tyin_A33____dumpstate_avx2 : seq atype :=
  [:: aarr U8 33; aword U64; aint; aarr U256 7 ].
Definition args_A33____dumpstate_avx2 : seq var_i :=
  [:: buf_66.(gv); offset_59.(gv); _LEN_41.(gv); st_48.(gv) ].
Definition tyout_A33____dumpstate_avx2 : seq atype :=
  [:: aarr U8 33; aword U64 ].
Definition res_A33____dumpstate_avx2 : seq var_i :=
  [:: buf_66.(gv); offset_59.(gv) ].

(* Body *)
Definition body_A33____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_40.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_41))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_66.(gv)
                                                                ; Lvar DELTA_40.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A33____a_ilen_write_upto32 [:: Pvar buf_66
                                                                    ; Pvar offset_59
                                                                    ; Pvar DELTA_40
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_48 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_41.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_41) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_66.(gv)
                                                                ; Lvar DELTA_40.(gv)
                                                                ; Lvar _LEN_41.(gv) ] A33____a_ilen_write_upto32 [:: Pvar buf_66
                                                                    ; Pvar offset_59
                                                                    ; Pvar DELTA_40
                                                                    ; Pvar _LEN_41
                                                                    ; Pget Aligned AAscale U256 st_48 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_66.(gv)
                                    ; Lvar DELTA_40.(gv)
                                    ; Lvar _LEN_41.(gv) ] A33____a_ilen_write_upto32 [:: Pvar buf_66
                                                                    ; Pvar offset_59
                                                                    ; Pvar DELTA_40
                                                                    ; Pvar _LEN_41
                                                                    ; Pget Aligned AAscale U256 st_48 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_41))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_10.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_48 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_15.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_48 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_6.(gv)) AT_none (aword U64) (Pvar t128_1_15))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_66.(gv)
                                                                ; Lvar DELTA_40.(gv)
                                                                ; Lvar _LEN_41.(gv) ] A33____a_ilen_write_upto8 [:: Pvar buf_66
                                                                    ; Pvar offset_59
                                                                    ; Pvar DELTA_40
                                                                    ; Pvar _LEN_41
                                                                    ; Pvar t_6 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_15.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_15
                                                                    ; Pvar t128_1_15 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_41))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_48 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_48 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_48 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_48 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_48 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_48 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_48 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_48 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_7
                                                                    ; Pvar t256_3_5
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_66.(gv)
                                                                  ; Lvar DELTA_40.(gv)
                                                                  ; Lvar _LEN_41.(gv) ] A33____a_ilen_write_upto32 [:: Pvar buf_66
                                                                    ; Pvar offset_59
                                                                    ; Pvar DELTA_40
                                                                    ; Pvar _LEN_41
                                                                    ; Pvar t256_4_4 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_41))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_6.(gv)) AT_none (aword U64) (Pvar t128_0_10))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_66.(gv)
                                                                    ; Lvar DELTA_40.(gv)
                                                                    ; Lvar _LEN_41.(gv) ] A33____a_ilen_write_upto8 [:: Pvar buf_66
                                                                    ; Pvar offset_59
                                                                    ; Pvar DELTA_40
                                                                    ; Pvar _LEN_41
                                                                    ; Pvar t_6 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_10
                                                                    ; Pvar t128_0_10 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_41))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_5
                                                                    ; Pvar t256_1_7
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_66.(gv)
                                                                    ; Lvar DELTA_40.(gv)
                                                                    ; Lvar _LEN_41.(gv) ] A33____a_ilen_write_upto32 [:: Pvar buf_66
                                                                    ; Pvar offset_59
                                                                    ; Pvar DELTA_40
                                                                    ; Pvar _LEN_41
                                                                    ; Pvar t256_4_4 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_41))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_6.(gv)) AT_none (aword U64) (Pvar t128_1_15))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_66.(gv)
                                                                    ; Lvar DELTA_40.(gv)
                                                                    ; Lvar _LEN_41.(gv) ] A33____a_ilen_write_upto8 [:: Pvar buf_66
                                                                    ; Pvar offset_59
                                                                    ; Pvar DELTA_40
                                                                    ; Pvar _LEN_41
                                                                    ; Pvar t_6 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_41))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_7
                                                                    ; Pvar t256_0_7
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_66.(gv)
                                                                    ; Lvar DELTA_40.(gv)
                                                                    ; Lvar _LEN_41.(gv) ] A33____a_ilen_write_upto32 [:: Pvar buf_66
                                                                    ; Pvar offset_59
                                                                    ; Pvar DELTA_40
                                                                    ; Pvar _LEN_41
                                                                    ; Pvar t256_4_4 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_41))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_6.(gv)) AT_none (aword U64) (Pvar t128_0_10))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_66.(gv)
                                                                    ; Lvar DELTA_40.(gv)
                                                                    ; Lvar _LEN_41.(gv) ] A33____a_ilen_write_upto8 [:: Pvar buf_66
                                                                    ; Pvar offset_59
                                                                    ; Pvar DELTA_40
                                                                    ; Pvar _LEN_41
                                                                    ; Pvar t_6 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_41))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_7
                                                                    ; Pvar t256_2_7
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_66.(gv)
                                                                    ; Lvar DELTA_40.(gv)
                                                                    ; Lvar _LEN_41.(gv) ] A33____a_ilen_write_upto32 [:: Pvar buf_66
                                                                    ; Pvar offset_59
                                                                    ; Pvar DELTA_40
                                                                    ; Pvar _LEN_41
                                                                    ; Pvar t256_4_4 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_59.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_59) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_40)))) ].

Definition fd_A33____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____dumpstate_avx2;
    f_params := args_A33____dumpstate_avx2;
    f_body := body_A33____dumpstate_avx2;
    f_tyout := tyout_A33____dumpstate_avx2;
    f_res := res_A33____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
