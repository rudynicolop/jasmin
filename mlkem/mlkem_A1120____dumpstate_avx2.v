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
Definition buf_15280 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15280).
Definition offset_15281 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15281).
Definition _LEN_15282 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15282).
Definition st_15283 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 15283).
Definition DELTA_15284 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15284).
Definition t128_0_15285 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15285).
Definition t128_1_15286 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15286).
Definition t_15287 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15287).
Definition t256_0_15288 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15288).
Definition t256_1_15289 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15289).
Definition t256_2_15290 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15290).
Definition t256_3_15291 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15291).
Definition t256_4_15292 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15292).

(* Signature *)
Definition tyin_A1120____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1120; aword U64; aint; aarr U256 7 ].
Definition args_A1120____dumpstate_avx2 : seq var_i :=
  [:: buf_15280.(gv); offset_15281.(gv); _LEN_15282.(gv); st_15283.(gv) ].
Definition tyout_A1120____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1120; aword U64 ].
Definition res_A1120____dumpstate_avx2 : seq var_i :=
  [:: buf_15280.(gv); offset_15281.(gv) ].

(* Body *)
Definition body_A1120____dumpstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_15284.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_15282))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_15280.(gv)
                                                                ; Lvar DELTA_15284.(gv)
                                                                ; Lnone dummy_var_info (aint) ] A1120____a_ilen_write_upto32 [:: Pvar buf_15280
                                                                    ; Pvar offset_15281
                                                                    ; Pvar DELTA_15284
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_15283 (Pconst (0)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15282.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_15282) (Pconst (8)%Z))) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf_15280.(gv)
                                                                ; Lvar DELTA_15284.(gv)
                                                                ; Lvar _LEN_15282.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_15280
                                                                    ; Pvar offset_15281
                                                                    ; Pvar DELTA_15284
                                                                    ; Pvar _LEN_15282
                                                                    ; Pget Aligned AAscale U256 st_15283 (Pconst (0)%Z) ]) ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_15280.(gv)
                                    ; Lvar DELTA_15284.(gv)
                                    ; Lvar _LEN_15282.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_15280
                                                                    ; Pvar offset_15281
                                                                    ; Pvar DELTA_15284
                                                                    ; Pvar _LEN_15282
                                                                    ; Pget Aligned AAscale U256 st_15283 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15282))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_15285.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 st_15283 (Pconst (2)%Z)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_15286.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_15283 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_15287.(gv)) AT_none (aword U64) (Pvar t128_1_15286))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_15280.(gv)
                                                                ; Lvar DELTA_15284.(gv)
                                                                ; Lvar _LEN_15282.(gv) ] A1120____a_ilen_write_upto8 [:: Pvar buf_15280
                                                                    ; Pvar offset_15281
                                                                    ; Pvar DELTA_15284
                                                                    ; Pvar _LEN_15282
                                                                    ; Pvar t_15287 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1_15286.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_15286
                                                                    ; Pvar t128_1_15286 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15282))
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_0_15288.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_15283 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_15283 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_1_15289.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_15283 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_15283 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_2_15290.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_15283 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_15283 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_3_15291.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_15283 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_15283 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t256_4_15292.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_15288
                                                                    ; Pvar t256_3_15291
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_15280.(gv)
                                                                  ; Lvar DELTA_15284.(gv)
                                                                  ; Lvar _LEN_15282.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_15280
                                                                    ; Pvar offset_15281
                                                                    ; Pvar DELTA_15284
                                                                    ; Pvar _LEN_15282
                                                                    ; Pvar t256_4_15292 ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15282))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_15287.(gv)) AT_none (aword U64) (Pvar t128_0_15285))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15280.(gv)
                                                                    ; Lvar DELTA_15284.(gv)
                                                                    ; Lvar _LEN_15282.(gv) ] A1120____a_ilen_write_upto8 [:: Pvar buf_15280
                                                                    ; Pvar offset_15281
                                                                    ; Pvar DELTA_15284
                                                                    ; Pvar _LEN_15282
                                                                    ; Pvar t_15287 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_0_15285.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_15285
                                                                    ; Pvar t128_0_15285 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15282))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_15292.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_15291
                                                                    ; Pvar t256_1_15289
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15280.(gv)
                                                                    ; Lvar DELTA_15284.(gv)
                                                                    ; Lvar _LEN_15282.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_15280
                                                                    ; Pvar offset_15281
                                                                    ; Pvar DELTA_15284
                                                                    ; Pvar _LEN_15282
                                                                    ; Pvar t256_4_15292 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15282))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_15287.(gv)) AT_none (aword U64) (Pvar t128_1_15286))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15280.(gv)
                                                                    ; Lvar DELTA_15284.(gv)
                                                                    ; Lvar _LEN_15282.(gv) ] A1120____a_ilen_write_upto8 [:: Pvar buf_15280
                                                                    ; Pvar offset_15281
                                                                    ; Pvar DELTA_15284
                                                                    ; Pvar _LEN_15282
                                                                    ; Pvar t_15287 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15282))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_15292.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_15290
                                                                    ; Pvar t256_0_15288
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15280.(gv)
                                                                    ; Lvar DELTA_15284.(gv)
                                                                    ; Lvar _LEN_15282.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_15280
                                                                    ; Pvar offset_15281
                                                                    ; Pvar DELTA_15284
                                                                    ; Pvar _LEN_15282
                                                                    ; Pvar t256_4_15292 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15282))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t_15287.(gv)) AT_none (aword U64) (Pvar t128_0_15285))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15280.(gv)
                                                                    ; Lvar DELTA_15284.(gv)
                                                                    ; Lvar _LEN_15282.(gv) ] A1120____a_ilen_write_upto8 [:: Pvar buf_15280
                                                                    ; Pvar offset_15281
                                                                    ; Pvar DELTA_15284
                                                                    ; Pvar _LEN_15282
                                                                    ; Pvar t_15287 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15282))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar t256_4_15292.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_15289
                                                                    ; Pvar t256_2_15290
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_15280.(gv)
                                                                    ; Lvar DELTA_15284.(gv)
                                                                    ; Lvar _LEN_15282.(gv) ] A1120____a_ilen_write_upto32 [:: Pvar buf_15280
                                                                    ; Pvar offset_15281
                                                                    ; Pvar DELTA_15284
                                                                    ; Pvar _LEN_15282
                                                                    ; Pvar t256_4_15292 ]) ]
                                                            [::]) ]
                                                          [::]) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_15281.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15281) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15284)))) ].

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
