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
Definition st_17472 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 17472).
Definition AT_17473 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17473).
Definition buf_17474 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17474).
Definition offset_17475 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17475).
Definition _LEN_17476 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17476).
Definition _TRAILB_17477 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17477).
Definition DELTA_17478 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17478).
Definition r0_17479 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17479).
Definition r1_17480 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17480).
Definition t64_2_17481 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17481).
Definition t128_1_17482 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17482).
Definition t128_2_17483 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17483).
Definition r3_17484 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17484).
Definition t64_3_17485 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17485).
Definition r4_17486 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17486).
Definition t64_4_17487 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17487).
Definition r5_17488 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17488).
Definition t64_5_17489 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17489).
Definition r6_17490 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17490).
Definition r2_17491 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17491).

(* Signature *)
Definition tyin_A32____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 32; aword U64; aint; aint ].
Definition args_A32____addstate_avx2 : seq var_i :=
  [:: st_17472.(gv)
    ; AT_17473.(gv)
    ; buf_17474.(gv)
    ; offset_17475.(gv)
    ; _LEN_17476.(gv)
    ; _TRAILB_17477.(gv) ].
Definition tyout_A32____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A32____addstate_avx2 : seq var_i :=
  [:: st_17472.(gv); AT_17473.(gv); offset_17475.(gv) ].

(* Body *)
Definition body_A32____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_17478.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_17473) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17478.(gv)
                                                                ; Lvar _LEN_17476.(gv)
                                                                ; Lvar _TRAILB_17477.(gv)
                                                                ; Lvar AT_17473.(gv)
                                                                ; Lvar r0_17479.(gv) ] A32____a_ilen_read_bcast_upto8_at [:: Pvar buf_17474
                                                                    ; Pvar offset_17475
                                                                    ; Pvar DELTA_17478
                                                                    ; Pvar _LEN_17476
                                                                    ; Pvar _TRAILB_17477
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_17473 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_17472.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_17472 (Pconst (0)%Z)) (Pvar r0_17479))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_17473) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17476)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17477) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17478.(gv)
                                                                ; Lvar _LEN_17476.(gv)
                                                                ; Lvar _TRAILB_17477.(gv)
                                                                ; Lvar AT_17473.(gv)
                                                                ; Lvar r1_17480.(gv) ] A32____a_ilen_read_upto32_at [:: Pvar buf_17474
                                                                    ; Pvar offset_17475
                                                                    ; Pvar DELTA_17478
                                                                    ; Pvar _LEN_17476
                                                                    ; Pvar _TRAILB_17477
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_17473 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_17472.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_17472 (Pconst (1)%Z)) (Pvar r1_17480))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17476)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17477) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17478.(gv)
                                                                ; Lvar _LEN_17476.(gv)
                                                                ; Lvar _TRAILB_17477.(gv)
                                                                ; Lvar AT_17473.(gv)
                                                                ; Lvar t64_2_17481.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_17474
                                                                    ; Pvar offset_17475
                                                                    ; Pvar DELTA_17478
                                                                    ; Pvar _LEN_17476
                                                                    ; Pvar _TRAILB_17477
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_17473 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_17482.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_17481)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_17483.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17476)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17477) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17478.(gv)
                                                                  ; Lvar _LEN_17476.(gv)
                                                                  ; Lvar _TRAILB_17477.(gv)
                                                                  ; Lvar AT_17473.(gv)
                                                                  ; Lvar r3_17484.(gv) ] A32____a_ilen_read_upto32_at [:: Pvar buf_17474
                                                                    ; Pvar offset_17475
                                                                    ; Pvar DELTA_17478
                                                                    ; Pvar _LEN_17476
                                                                    ; Pvar _TRAILB_17477
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_17473 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17478.(gv)
                                                                  ; Lvar _LEN_17476.(gv)
                                                                  ; Lvar _TRAILB_17477.(gv)
                                                                  ; Lvar AT_17473.(gv)
                                                                  ; Lvar t64_3_17485.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_17474
                                                                    ; Pvar offset_17475
                                                                    ; Pvar DELTA_17478
                                                                    ; Pvar _LEN_17476
                                                                    ; Pvar _TRAILB_17477
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_17473 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_17483.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_17485)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17478.(gv)
                                                                  ; Lvar _LEN_17476.(gv)
                                                                  ; Lvar _TRAILB_17477.(gv)
                                                                  ; Lvar AT_17473.(gv)
                                                                  ; Lvar r4_17486.(gv) ] A32____a_ilen_read_upto32_at [:: Pvar buf_17474
                                                                    ; Pvar offset_17475
                                                                    ; Pvar DELTA_17478
                                                                    ; Pvar _LEN_17476
                                                                    ; Pvar _TRAILB_17477
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_17473 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17478.(gv)
                                                                  ; Lvar _LEN_17476.(gv)
                                                                  ; Lvar _TRAILB_17477.(gv)
                                                                  ; Lvar AT_17473.(gv)
                                                                  ; Lvar t64_4_17487.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_17474
                                                                    ; Pvar offset_17475
                                                                    ; Pvar DELTA_17478
                                                                    ; Pvar _LEN_17476
                                                                    ; Pvar _TRAILB_17477
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_17473 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_17482.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_17482
                                                                    ; Pvar t64_4_17487
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17478.(gv)
                                                                  ; Lvar _LEN_17476.(gv)
                                                                  ; Lvar _TRAILB_17477.(gv)
                                                                  ; Lvar AT_17473.(gv)
                                                                  ; Lvar r5_17488.(gv) ] A32____a_ilen_read_upto32_at [:: Pvar buf_17474
                                                                    ; Pvar offset_17475
                                                                    ; Pvar DELTA_17478
                                                                    ; Pvar _LEN_17476
                                                                    ; Pvar _TRAILB_17477
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_17473 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17478.(gv)
                                                                  ; Lvar _LEN_17476.(gv)
                                                                  ; Lvar _TRAILB_17477.(gv)
                                                                  ; Lvar AT_17473.(gv)
                                                                  ; Lvar t64_5_17489.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_17474
                                                                    ; Pvar offset_17475
                                                                    ; Pvar DELTA_17478
                                                                    ; Pvar _LEN_17476
                                                                    ; Pvar _TRAILB_17477
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_17473 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_17483.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_17483
                                                                    ; Pvar t64_5_17489
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17478.(gv)
                                                                  ; Lvar _LEN_17476.(gv)
                                                                  ; Lvar _TRAILB_17477.(gv)
                                                                  ; Lvar AT_17473.(gv)
                                                                  ; Lvar r6_17490.(gv) ] A32____a_ilen_read_upto32_at [:: Pvar buf_17474
                                                                    ; Pvar offset_17475
                                                                    ; Pvar DELTA_17478
                                                                    ; Pvar _LEN_17476
                                                                    ; Pvar _TRAILB_17477
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_17473 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_17472.(gv) ] __addstate_r3456_avx2 [:: Pvar st_17472
                                                                    ; Pvar r3_17484
                                                                    ; Pvar r4_17486
                                                                    ; Pvar r5_17488
                                                                    ; Pvar r6_17490 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_17491.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_17483)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_17491.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_17491
                                                                    ; Pvar t128_1_17482
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_17472.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_17472 (Pconst (2)%Z)) (Pvar r2_17491))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_17475.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17475) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17478)))) ].

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
