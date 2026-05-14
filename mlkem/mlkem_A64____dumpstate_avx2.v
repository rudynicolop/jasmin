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
Definition buf_16673 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 16673).
Definition offset_16674 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16674).
Definition _LEN_16675 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16675).
Definition st_16676 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16676).
Definition DELTA_16677 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16677).
Definition t128_0_16678 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16678).
Definition t128_1_16679 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16679).
Definition t_16680 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16680).
Definition t256_0_16681 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16681).
Definition t256_1_16682 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16682).
Definition t256_2_16683 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16683).
Definition t256_3_16684 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16684).
Definition t256_4_16685 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16685).

(* Signature *)
Definition tyin_A64____dumpstate_avx2 : seq atype :=
  [:: aarr U8 64; aword U64; aint; aarr U256 7 ].
Definition args_A64____dumpstate_avx2 : seq var_i :=
  [:: buf_16673.(gv); offset_16674.(gv); _LEN_16675.(gv); st_16676.(gv) ].
Definition tyout_A64____dumpstate_avx2 : seq atype :=
  [:: aarr U8 64; aword U64 ].
Definition res_A64____dumpstate_avx2 : seq var_i :=
  [:: buf_16673.(gv); offset_16674.(gv) ].

(* Body *)
Definition body_A64____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_16677.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_16675))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_16673.(gv)
                                                                ; Lvar DELTA_16677.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A64____a_ilen_write_upto32 [:: Pvar buf_16673
                                                                    ; Pvar offset_16674
                                                                    ; Pvar DELTA_16677
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_16676 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_16675.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_16675) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_16673.(gv)
                                                                ; Lvar DELTA_16677.(gv)
                                                                ; Lvar _LEN_16675.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_16673
                                                                    ; Pvar offset_16674
                                                                    ; Pvar DELTA_16677
                                                                    ; Pvar _LEN_16675
                                                                    ; Pget Aligned AAscale U256 st_16676 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_16673.(gv)
                                    ; Lvar DELTA_16677.(gv)
                                    ; Lvar _LEN_16675.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_16673
                                                                    ; Pvar offset_16674
                                                                    ; Pvar DELTA_16677
                                                                    ; Pvar _LEN_16675
                                                                    ; Pget Aligned AAscale U256 st_16676 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16675))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_16678.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_16676 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_16679.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_16676 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_16680.(gv)) AT_none (aword U64) (Pvar t128_1_16679))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_16673.(gv)
                                                                ; Lvar DELTA_16677.(gv)
                                                                ; Lvar _LEN_16675.(gv) ] A64____a_ilen_write_upto8 [:: Pvar buf_16673
                                                                    ; Pvar offset_16674
                                                                    ; Pvar DELTA_16677
                                                                    ; Pvar _LEN_16675
                                                                    ; Pvar t_16680 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_16679.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_16679
                                                                    ; Pvar t128_1_16679 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16675))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_16681.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16676 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16676 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_16682.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16676 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16676 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_16683.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16676 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16676 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_16684.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16676 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16676 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_16685.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_16681
                                                                    ; Pvar t256_3_16684
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_16673.(gv)
                                                                  ; Lvar DELTA_16677.(gv)
                                                                  ; Lvar _LEN_16675.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_16673
                                                                    ; Pvar offset_16674
                                                                    ; Pvar DELTA_16677
                                                                    ; Pvar _LEN_16675
                                                                    ; Pvar t256_4_16685 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16675))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_16680.(gv)) AT_none (aword U64) (Pvar t128_0_16678))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_16673.(gv)
                                                                    ; Lvar DELTA_16677.(gv)
                                                                    ; Lvar _LEN_16675.(gv) ] A64____a_ilen_write_upto8 [:: Pvar buf_16673
                                                                    ; Pvar offset_16674
                                                                    ; Pvar DELTA_16677
                                                                    ; Pvar _LEN_16675
                                                                    ; Pvar t_16680 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_16678.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_16678
                                                                    ; Pvar t128_0_16678 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16675))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_16685.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_16684
                                                                    ; Pvar t256_1_16682
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_16673.(gv)
                                                                    ; Lvar DELTA_16677.(gv)
                                                                    ; Lvar _LEN_16675.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_16673
                                                                    ; Pvar offset_16674
                                                                    ; Pvar DELTA_16677
                                                                    ; Pvar _LEN_16675
                                                                    ; Pvar t256_4_16685 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16675))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_16680.(gv)) AT_none (aword U64) (Pvar t128_1_16679))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_16673.(gv)
                                                                    ; Lvar DELTA_16677.(gv)
                                                                    ; Lvar _LEN_16675.(gv) ] A64____a_ilen_write_upto8 [:: Pvar buf_16673
                                                                    ; Pvar offset_16674
                                                                    ; Pvar DELTA_16677
                                                                    ; Pvar _LEN_16675
                                                                    ; Pvar t_16680 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16675))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_16685.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_16683
                                                                    ; Pvar t256_0_16681
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_16673.(gv)
                                                                    ; Lvar DELTA_16677.(gv)
                                                                    ; Lvar _LEN_16675.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_16673
                                                                    ; Pvar offset_16674
                                                                    ; Pvar DELTA_16677
                                                                    ; Pvar _LEN_16675
                                                                    ; Pvar t256_4_16685 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16675))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_16680.(gv)) AT_none (aword U64) (Pvar t128_0_16678))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_16673.(gv)
                                                                    ; Lvar DELTA_16677.(gv)
                                                                    ; Lvar _LEN_16675.(gv) ] A64____a_ilen_write_upto8 [:: Pvar buf_16673
                                                                    ; Pvar offset_16674
                                                                    ; Pvar DELTA_16677
                                                                    ; Pvar _LEN_16675
                                                                    ; Pvar t_16680 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16675))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_16685.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_16682
                                                                    ; Pvar t256_2_16683
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_16673.(gv)
                                                                    ; Lvar DELTA_16677.(gv)
                                                                    ; Lvar _LEN_16675.(gv) ] A64____a_ilen_write_upto32 [:: Pvar buf_16673
                                                                    ; Pvar offset_16674
                                                                    ; Pvar DELTA_16677
                                                                    ; Pvar _LEN_16675
                                                                    ; Pvar t256_4_16685 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_16674.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16674) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16677)))) ].

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
