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
Definition buf_15662 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15662).
Definition offset_15663 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15663).
Definition _LEN_15664 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15664).
Definition st_15665 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 15665).
Definition DELTA_15666 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15666).
Definition t128_0_15667 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15667).
Definition t128_1_15668 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15668).
Definition t_15669 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15669).
Definition t256_0_15670 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15670).
Definition t256_1_15671 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15671).
Definition t256_2_15672 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15672).
Definition t256_3_15673 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15673).
Definition t256_4_15674 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15674).

(* Signature *)
Definition tyin_A1568____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aarr U256 7 ].
Definition args_A1568____dumpstate_avx2 : seq var_i :=
  [:: buf_15662.(gv); offset_15663.(gv); _LEN_15664.(gv); st_15665.(gv) ].
Definition tyout_A1568____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1568; aword U64 ].
Definition res_A1568____dumpstate_avx2 : seq var_i :=
  [:: buf_15662.(gv); offset_15663.(gv) ].

(* Body *)
Definition body_A1568____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_15666.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_15664))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_15662.(gv)
                                                                ; Lvar DELTA_15666.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A1568____a_ilen_write_upto32 [:: Pvar buf_15662
                                                                    ; Pvar offset_15663
                                                                    ; Pvar DELTA_15666
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_15665 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15664.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_15664) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_15662.(gv)
                                                                ; Lvar DELTA_15666.(gv)
                                                                ; Lvar _LEN_15664.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_15662
                                                                    ; Pvar offset_15663
                                                                    ; Pvar DELTA_15666
                                                                    ; Pvar _LEN_15664
                                                                    ; Pget Aligned AAscale U256 st_15665 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_15662.(gv)
                                    ; Lvar DELTA_15666.(gv)
                                    ; Lvar _LEN_15664.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_15662
                                                                    ; Pvar offset_15663
                                                                    ; Pvar DELTA_15666
                                                                    ; Pvar _LEN_15664
                                                                    ; Pget Aligned AAscale U256 st_15665 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15664))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_15667.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_15665 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_15668.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_15665 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_15669.(gv)) AT_none (aword U64) (Pvar t128_1_15668))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_15662.(gv)
                                                                ; Lvar DELTA_15666.(gv)
                                                                ; Lvar _LEN_15664.(gv) ] A1568____a_ilen_write_upto8 [:: Pvar buf_15662
                                                                    ; Pvar offset_15663
                                                                    ; Pvar DELTA_15666
                                                                    ; Pvar _LEN_15664
                                                                    ; Pvar t_15669 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_15668.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_15668
                                                                    ; Pvar t128_1_15668 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15664))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_15670.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_15665 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_15665 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_15671.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_15665 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_15665 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_15672.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_15665 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_15665 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_15673.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_15665 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_15665 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_15674.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_15670
                                                                    ; Pvar t256_3_15673
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_15662.(gv)
                                                                  ; Lvar DELTA_15666.(gv)
                                                                  ; Lvar _LEN_15664.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_15662
                                                                    ; Pvar offset_15663
                                                                    ; Pvar DELTA_15666
                                                                    ; Pvar _LEN_15664
                                                                    ; Pvar t256_4_15674 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15664))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_15669.(gv)) AT_none (aword U64) (Pvar t128_0_15667))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15662.(gv)
                                                                    ; Lvar DELTA_15666.(gv)
                                                                    ; Lvar _LEN_15664.(gv) ] A1568____a_ilen_write_upto8 [:: Pvar buf_15662
                                                                    ; Pvar offset_15663
                                                                    ; Pvar DELTA_15666
                                                                    ; Pvar _LEN_15664
                                                                    ; Pvar t_15669 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_15667.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_15667
                                                                    ; Pvar t128_0_15667 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15664))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_15674.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_15673
                                                                    ; Pvar t256_1_15671
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15662.(gv)
                                                                    ; Lvar DELTA_15666.(gv)
                                                                    ; Lvar _LEN_15664.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_15662
                                                                    ; Pvar offset_15663
                                                                    ; Pvar DELTA_15666
                                                                    ; Pvar _LEN_15664
                                                                    ; Pvar t256_4_15674 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15664))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_15669.(gv)) AT_none (aword U64) (Pvar t128_1_15668))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15662.(gv)
                                                                    ; Lvar DELTA_15666.(gv)
                                                                    ; Lvar _LEN_15664.(gv) ] A1568____a_ilen_write_upto8 [:: Pvar buf_15662
                                                                    ; Pvar offset_15663
                                                                    ; Pvar DELTA_15666
                                                                    ; Pvar _LEN_15664
                                                                    ; Pvar t_15669 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15664))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_15674.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_15672
                                                                    ; Pvar t256_0_15670
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15662.(gv)
                                                                    ; Lvar DELTA_15666.(gv)
                                                                    ; Lvar _LEN_15664.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_15662
                                                                    ; Pvar offset_15663
                                                                    ; Pvar DELTA_15666
                                                                    ; Pvar _LEN_15664
                                                                    ; Pvar t256_4_15674 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15664))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_15669.(gv)) AT_none (aword U64) (Pvar t128_0_15667))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15662.(gv)
                                                                    ; Lvar DELTA_15666.(gv)
                                                                    ; Lvar _LEN_15664.(gv) ] A1568____a_ilen_write_upto8 [:: Pvar buf_15662
                                                                    ; Pvar offset_15663
                                                                    ; Pvar DELTA_15666
                                                                    ; Pvar _LEN_15664
                                                                    ; Pvar t_15669 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15664))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_15674.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_15671
                                                                    ; Pvar t256_2_15672
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15662.(gv)
                                                                    ; Lvar DELTA_15666.(gv)
                                                                    ; Lvar _LEN_15664.(gv) ] A1568____a_ilen_write_upto32 [:: Pvar buf_15662
                                                                    ; Pvar offset_15663
                                                                    ; Pvar DELTA_15666
                                                                    ; Pvar _LEN_15664
                                                                    ; Pvar t256_4_15674 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_15663.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15663) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15666)))) ].

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
