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

(* A1120____dumpstate_avx2 *)
(* Local variables *)
Definition buf_134 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15280).
Definition offset_138 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15281).
Definition _LEN_85 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15282).
Definition st_92 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 15283).
Definition DELTA_93 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15284).
Definition t128_0_20 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15285).
Definition t128_1_30 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15286).
Definition t_11 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15287).
Definition t256_0_12 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15288).
Definition t256_1_12 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15289).
Definition t256_2_12 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15290).
Definition t256_3_10 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15291).
Definition t256_4_9 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15292).

(* Signature *)
Definition tyin_A1120____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1120; aword U64; aint; aarr U256 7 ].
Definition args_A1120____dumpstate_avx2 : seq var_i :=
  [:: buf_134.(gv); offset_138.(gv); _LEN_85.(gv); st_92.(gv) ].
Definition tyout_A1120____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1120; aword U64 ].
Definition res_A1120____dumpstate_avx2 : seq var_i :=
  [:: buf_134.(gv); offset_138.(gv) ].

(* Body *)
Definition body_A1120____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_93.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_85))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_134.(gv)
                                                                ; Lvar DELTA_93.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A1120____a_ilen_write_upto32 [:: Pvar buf_134
                                                                    ; Pvar offset_138
                                                                    ; Pvar DELTA_93
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_92 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_85.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_85) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_134.(gv)
                                                                ; Lvar DELTA_93.(gv)
                                                                ; Lvar _LEN_85.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_134
                                                                    ; Pvar offset_138
                                                                    ; Pvar DELTA_93
                                                                    ; Pvar _LEN_85
                                                                    ; Pget Aligned AAscale U256 st_92 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_134.(gv)
                                    ; Lvar DELTA_93.(gv)
                                    ; Lvar _LEN_85.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_134
                                                                    ; Pvar offset_138
                                                                    ; Pvar DELTA_93
                                                                    ; Pvar _LEN_85
                                                                    ; Pget Aligned AAscale U256 st_92 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_85))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_20.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_92 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_30.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_92 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_11.(gv)) AT_none (aword U64) (Pvar t128_1_30))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_134.(gv)
                                                                ; Lvar DELTA_93.(gv)
                                                                ; Lvar _LEN_85.(gv) ] A1120____a_ilen_write_upto8 [:: Pvar buf_134
                                                                    ; Pvar offset_138
                                                                    ; Pvar DELTA_93
                                                                    ; Pvar _LEN_85
                                                                    ; Pvar t_11 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_30.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_30
                                                                    ; Pvar t128_1_30 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_85))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_12.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_92 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_92 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_12.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_92 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_92 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_12.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_92 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_92 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_92 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_92 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_12
                                                                    ; Pvar t256_3_10
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_134.(gv)
                                                                  ; Lvar DELTA_93.(gv)
                                                                  ; Lvar _LEN_85.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_134
                                                                    ; Pvar offset_138
                                                                    ; Pvar DELTA_93
                                                                    ; Pvar _LEN_85
                                                                    ; Pvar t256_4_9 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_85))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_11.(gv)) AT_none (aword U64) (Pvar t128_0_20))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_134.(gv)
                                                                    ; Lvar DELTA_93.(gv)
                                                                    ; Lvar _LEN_85.(gv) ] A1120____a_ilen_write_upto8 [:: Pvar buf_134
                                                                    ; Pvar offset_138
                                                                    ; Pvar DELTA_93
                                                                    ; Pvar _LEN_85
                                                                    ; Pvar t_11 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_20.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_20
                                                                    ; Pvar t128_0_20 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_85))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_10
                                                                    ; Pvar t256_1_12
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_134.(gv)
                                                                    ; Lvar DELTA_93.(gv)
                                                                    ; Lvar _LEN_85.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_134
                                                                    ; Pvar offset_138
                                                                    ; Pvar DELTA_93
                                                                    ; Pvar _LEN_85
                                                                    ; Pvar t256_4_9 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_85))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_11.(gv)) AT_none (aword U64) (Pvar t128_1_30))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_134.(gv)
                                                                    ; Lvar DELTA_93.(gv)
                                                                    ; Lvar _LEN_85.(gv) ] A1120____a_ilen_write_upto8 [:: Pvar buf_134
                                                                    ; Pvar offset_138
                                                                    ; Pvar DELTA_93
                                                                    ; Pvar _LEN_85
                                                                    ; Pvar t_11 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_85))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_12
                                                                    ; Pvar t256_0_12
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_134.(gv)
                                                                    ; Lvar DELTA_93.(gv)
                                                                    ; Lvar _LEN_85.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_134
                                                                    ; Pvar offset_138
                                                                    ; Pvar DELTA_93
                                                                    ; Pvar _LEN_85
                                                                    ; Pvar t256_4_9 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_85))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_11.(gv)) AT_none (aword U64) (Pvar t128_0_20))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_134.(gv)
                                                                    ; Lvar DELTA_93.(gv)
                                                                    ; Lvar _LEN_85.(gv) ] A1120____a_ilen_write_upto8 [:: Pvar buf_134
                                                                    ; Pvar offset_138
                                                                    ; Pvar DELTA_93
                                                                    ; Pvar _LEN_85
                                                                    ; Pvar t_11 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_85))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_12
                                                                    ; Pvar t256_2_12
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_134.(gv)
                                                                    ; Lvar DELTA_93.(gv)
                                                                    ; Lvar _LEN_85.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_134
                                                                    ; Pvar offset_138
                                                                    ; Pvar DELTA_93
                                                                    ; Pvar _LEN_85
                                                                    ; Pvar t256_4_9 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_138.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_138) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_93)))) ].

Definition fd_A1120____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____dumpstate_avx2;
    f_params := args_A1120____dumpstate_avx2;
    f_body := body_A1120____dumpstate_avx2;
    f_tyout := tyout_A1120____dumpstate_avx2;
    f_res := res_A1120____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
