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

(* A32____addstate_avx2 *)
(* Local variables *)
Definition st_36 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 17472).
Definition AT_33 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17473).
Definition buf_50 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17474).
Definition offset_40 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17475).
Definition _LEN_29 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17476).
Definition _TRAILB_17 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17477).
Definition DELTA_28 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17478).
Definition r0_7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17479).
Definition r1_7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17480).
Definition t64_2_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17481).
Definition t128_1_11 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17482).
Definition t128_2_2 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17483).
Definition r3_7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17484).
Definition t64_3_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17485).
Definition r4_7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17486).
Definition t64_4_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17487).
Definition r5_7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17488).
Definition t64_5_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17489).
Definition r6_7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17490).
Definition r2_4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17491).

(* Signature *)
Definition tyin_A32____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 32; aword U64; aint; aint ].
Definition args_A32____addstate_avx2 : seq var_i :=
  [:: st_36.(gv)
    ; AT_33.(gv)
    ; buf_50.(gv)
    ; offset_40.(gv)
    ; _LEN_29.(gv)
    ; _TRAILB_17.(gv) ].
Definition tyout_A32____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A32____addstate_avx2 : seq var_i :=
  [:: st_36.(gv); AT_33.(gv); offset_40.(gv) ].

(* Body *)
Definition body_A32____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_28.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_33) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_28.(gv)
                                                                ; Lvar _LEN_29.(gv)
                                                                ; Lvar _TRAILB_17.(gv)
                                                                ; Lvar AT_33.(gv)
                                                                ; Lvar r0_7.(gv) ] A32____a_ilen_read_bcast_upto8_at [:: Pvar buf_50
                                                                    ; Pvar offset_40
                                                                    ; Pvar DELTA_28
                                                                    ; Pvar _LEN_29
                                                                    ; Pvar _TRAILB_17
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_33 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_36.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_36 (Pconst (0)%Z)) (Pvar r0_7))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_33) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_29)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_28.(gv)
                                                                ; Lvar _LEN_29.(gv)
                                                                ; Lvar _TRAILB_17.(gv)
                                                                ; Lvar AT_33.(gv)
                                                                ; Lvar r1_7.(gv) ] A32____a_ilen_read_upto32_at [:: Pvar buf_50
                                                                    ; Pvar offset_40
                                                                    ; Pvar DELTA_28
                                                                    ; Pvar _LEN_29
                                                                    ; Pvar _TRAILB_17
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_33 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_36.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_36 (Pconst (1)%Z)) (Pvar r1_7))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_29)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_28.(gv)
                                                                ; Lvar _LEN_29.(gv)
                                                                ; Lvar _TRAILB_17.(gv)
                                                                ; Lvar AT_33.(gv)
                                                                ; Lvar t64_2_2.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_50
                                                                    ; Pvar offset_40
                                                                    ; Pvar DELTA_28
                                                                    ; Pvar _LEN_29
                                                                    ; Pvar _TRAILB_17
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_33 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_11.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_2)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_2.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_29)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_28.(gv)
                                                                  ; Lvar _LEN_29.(gv)
                                                                  ; Lvar _TRAILB_17.(gv)
                                                                  ; Lvar AT_33.(gv)
                                                                  ; Lvar r3_7.(gv) ] A32____a_ilen_read_upto32_at [:: Pvar buf_50
                                                                    ; Pvar offset_40
                                                                    ; Pvar DELTA_28
                                                                    ; Pvar _LEN_29
                                                                    ; Pvar _TRAILB_17
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_33 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_28.(gv)
                                                                  ; Lvar _LEN_29.(gv)
                                                                  ; Lvar _TRAILB_17.(gv)
                                                                  ; Lvar AT_33.(gv)
                                                                  ; Lvar t64_3_2.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_50
                                                                    ; Pvar offset_40
                                                                    ; Pvar DELTA_28
                                                                    ; Pvar _LEN_29
                                                                    ; Pvar _TRAILB_17
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_33 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_2.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_2)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_28.(gv)
                                                                  ; Lvar _LEN_29.(gv)
                                                                  ; Lvar _TRAILB_17.(gv)
                                                                  ; Lvar AT_33.(gv)
                                                                  ; Lvar r4_7.(gv) ] A32____a_ilen_read_upto32_at [:: Pvar buf_50
                                                                    ; Pvar offset_40
                                                                    ; Pvar DELTA_28
                                                                    ; Pvar _LEN_29
                                                                    ; Pvar _TRAILB_17
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_33 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_28.(gv)
                                                                  ; Lvar _LEN_29.(gv)
                                                                  ; Lvar _TRAILB_17.(gv)
                                                                  ; Lvar AT_33.(gv)
                                                                  ; Lvar t64_4_2.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_50
                                                                    ; Pvar offset_40
                                                                    ; Pvar DELTA_28
                                                                    ; Pvar _LEN_29
                                                                    ; Pvar _TRAILB_17
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_33 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_11
                                                                    ; Pvar t64_4_2
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_28.(gv)
                                                                  ; Lvar _LEN_29.(gv)
                                                                  ; Lvar _TRAILB_17.(gv)
                                                                  ; Lvar AT_33.(gv)
                                                                  ; Lvar r5_7.(gv) ] A32____a_ilen_read_upto32_at [:: Pvar buf_50
                                                                    ; Pvar offset_40
                                                                    ; Pvar DELTA_28
                                                                    ; Pvar _LEN_29
                                                                    ; Pvar _TRAILB_17
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_33 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_28.(gv)
                                                                  ; Lvar _LEN_29.(gv)
                                                                  ; Lvar _TRAILB_17.(gv)
                                                                  ; Lvar AT_33.(gv)
                                                                  ; Lvar t64_5_2.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_50
                                                                    ; Pvar offset_40
                                                                    ; Pvar DELTA_28
                                                                    ; Pvar _LEN_29
                                                                    ; Pvar _TRAILB_17
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_33 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_2
                                                                    ; Pvar t64_5_2
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_28.(gv)
                                                                  ; Lvar _LEN_29.(gv)
                                                                  ; Lvar _TRAILB_17.(gv)
                                                                  ; Lvar AT_33.(gv)
                                                                  ; Lvar r6_7.(gv) ] A32____a_ilen_read_upto32_at [:: Pvar buf_50
                                                                    ; Pvar offset_40
                                                                    ; Pvar DELTA_28
                                                                    ; Pvar _LEN_29
                                                                    ; Pvar _TRAILB_17
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_33 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_36.(gv) ] __addstate_r3456_avx2 [:: Pvar st_36
                                                                    ; Pvar r3_7
                                                                    ; Pvar r4_7
                                                                    ; Pvar r5_7
                                                                    ; Pvar r6_7 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_4.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_2)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_4.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_4
                                                                    ; Pvar t128_1_11
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_36.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_36 (Pconst (2)%Z)) (Pvar r2_4))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_40.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_40) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_28)))) ].

Definition fd_A32____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____addstate_avx2;
    f_params := args_A32____addstate_avx2;
    f_body := body_A32____addstate_avx2;
    f_tyout := tyout_A32____addstate_avx2;
    f_res := res_A32____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
