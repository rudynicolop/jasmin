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

(* A2____dumpstate_avx2 *)
(* Local variables *)
Definition buf_17819 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17819).
Definition offset_17820 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17820).
Definition _LEN_17821 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17821).
Definition st_17822 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 17822).
Definition DELTA_17823 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17823).
Definition t128_0_17824 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17824).
Definition t128_1_17825 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17825).
Definition t_17826 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17826).
Definition t256_0_17827 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17827).
Definition t256_1_17828 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17828).
Definition t256_2_17829 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17829).
Definition t256_3_17830 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17830).
Definition t256_4_17831 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17831).

(* Signature *)
Definition tyin_A2____dumpstate_avx2 : seq atype :=
  [:: aarr U8 2; aword U64; aint; aarr U256 7 ].
Definition args_A2____dumpstate_avx2 : seq var_i :=
  [:: buf_17819.(gv); offset_17820.(gv); _LEN_17821.(gv); st_17822.(gv) ].
Definition tyout_A2____dumpstate_avx2 : seq atype :=
  [:: aarr U8 2; aword U64 ].
Definition res_A2____dumpstate_avx2 : seq var_i :=
  [:: buf_17819.(gv); offset_17820.(gv) ].

(* Body *)
Definition body_A2____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_17823.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_17821))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_17819.(gv)
                                                                ; Lvar DELTA_17823.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A2____a_ilen_write_upto32 [:: Pvar buf_17819
                                                                    ; Pvar offset_17820
                                                                    ; Pvar DELTA_17823
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_17822 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17821.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_17821) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_17819.(gv)
                                                                ; Lvar DELTA_17823.(gv)
                                                                ; Lvar _LEN_17821.(gv) ] A2____a_ilen_write_upto32 [:: Pvar buf_17819
                                                                    ; Pvar offset_17820
                                                                    ; Pvar DELTA_17823
                                                                    ; Pvar _LEN_17821
                                                                    ; Pget Aligned AAscale U256 st_17822 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_17819.(gv)
                                    ; Lvar DELTA_17823.(gv)
                                    ; Lvar _LEN_17821.(gv) ] A2____a_ilen_write_upto32 [:: Pvar buf_17819
                                                                    ; Pvar offset_17820
                                                                    ; Pvar DELTA_17823
                                                                    ; Pvar _LEN_17821
                                                                    ; Pget Aligned AAscale U256 st_17822 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17821))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_17824.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_17822 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_17825.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_17822 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_17826.(gv)) AT_none (aword U64) (Pvar t128_1_17825))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_17819.(gv)
                                                                ; Lvar DELTA_17823.(gv)
                                                                ; Lvar _LEN_17821.(gv) ] A2____a_ilen_write_upto8 [:: Pvar buf_17819
                                                                    ; Pvar offset_17820
                                                                    ; Pvar DELTA_17823
                                                                    ; Pvar _LEN_17821
                                                                    ; Pvar t_17826 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_17825.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_17825
                                                                    ; Pvar t128_1_17825 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17821))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_17827.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_17822 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_17822 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_17828.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_17822 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_17822 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_17829.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_17822 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_17822 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_17830.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_17822 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_17822 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_17831.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_17827
                                                                    ; Pvar t256_3_17830
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_17819.(gv)
                                                                  ; Lvar DELTA_17823.(gv)
                                                                  ; Lvar _LEN_17821.(gv) ] A2____a_ilen_write_upto32 [:: Pvar buf_17819
                                                                    ; Pvar offset_17820
                                                                    ; Pvar DELTA_17823
                                                                    ; Pvar _LEN_17821
                                                                    ; Pvar t256_4_17831 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17821))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_17826.(gv)) AT_none (aword U64) (Pvar t128_0_17824))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_17819.(gv)
                                                                    ; Lvar DELTA_17823.(gv)
                                                                    ; Lvar _LEN_17821.(gv) ] A2____a_ilen_write_upto8 [:: Pvar buf_17819
                                                                    ; Pvar offset_17820
                                                                    ; Pvar DELTA_17823
                                                                    ; Pvar _LEN_17821
                                                                    ; Pvar t_17826 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_17824.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_17824
                                                                    ; Pvar t128_0_17824 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17821))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_17831.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_17830
                                                                    ; Pvar t256_1_17828
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_17819.(gv)
                                                                    ; Lvar DELTA_17823.(gv)
                                                                    ; Lvar _LEN_17821.(gv) ] A2____a_ilen_write_upto32 [:: Pvar buf_17819
                                                                    ; Pvar offset_17820
                                                                    ; Pvar DELTA_17823
                                                                    ; Pvar _LEN_17821
                                                                    ; Pvar t256_4_17831 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17821))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_17826.(gv)) AT_none (aword U64) (Pvar t128_1_17825))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_17819.(gv)
                                                                    ; Lvar DELTA_17823.(gv)
                                                                    ; Lvar _LEN_17821.(gv) ] A2____a_ilen_write_upto8 [:: Pvar buf_17819
                                                                    ; Pvar offset_17820
                                                                    ; Pvar DELTA_17823
                                                                    ; Pvar _LEN_17821
                                                                    ; Pvar t_17826 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17821))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_17831.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_17829
                                                                    ; Pvar t256_0_17827
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_17819.(gv)
                                                                    ; Lvar DELTA_17823.(gv)
                                                                    ; Lvar _LEN_17821.(gv) ] A2____a_ilen_write_upto32 [:: Pvar buf_17819
                                                                    ; Pvar offset_17820
                                                                    ; Pvar DELTA_17823
                                                                    ; Pvar _LEN_17821
                                                                    ; Pvar t256_4_17831 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17821))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_17826.(gv)) AT_none (aword U64) (Pvar t128_0_17824))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_17819.(gv)
                                                                    ; Lvar DELTA_17823.(gv)
                                                                    ; Lvar _LEN_17821.(gv) ] A2____a_ilen_write_upto8 [:: Pvar buf_17819
                                                                    ; Pvar offset_17820
                                                                    ; Pvar DELTA_17823
                                                                    ; Pvar _LEN_17821
                                                                    ; Pvar t_17826 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17821))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_17831.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_17828
                                                                    ; Pvar t256_2_17829
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_17819.(gv)
                                                                    ; Lvar DELTA_17823.(gv)
                                                                    ; Lvar _LEN_17821.(gv) ] A2____a_ilen_write_upto32 [:: Pvar buf_17819
                                                                    ; Pvar offset_17820
                                                                    ; Pvar DELTA_17823
                                                                    ; Pvar _LEN_17821
                                                                    ; Pvar t256_4_17831 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_17820.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17820) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17823)))) ].

Definition fd_A2____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____dumpstate_avx2;
    f_params := args_A2____dumpstate_avx2;
    f_body := body_A2____dumpstate_avx2;
    f_tyout := tyout_A2____dumpstate_avx2;
    f_res := res_A2____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
