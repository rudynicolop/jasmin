From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* A128____addstate_avx2 *)
(* Local variables *)
Definition st_16461 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16461).
Definition AT_16462 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16462).
Definition buf_16463 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16463).
Definition offset_16464 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16464).
Definition _LEN_16465 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16465).
Definition _TRAILB_16466 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16466).
Definition DELTA_16467 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16467).
Definition r0_16468 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16468).
Definition r1_16469 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16469).
Definition t64_2_16470 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16470).
Definition t128_1_16471 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16471).
Definition t128_2_16472 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16472).
Definition r3_16473 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16473).
Definition t64_3_16474 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16474).
Definition r4_16475 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16475).
Definition t64_4_16476 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16476).
Definition r5_16477 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16477).
Definition t64_5_16478 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16478).
Definition r6_16479 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16479).
Definition r2_16480 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16480).

(* Signature *)
Definition tyin_A128____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 128; aword U64; aint; aint ].
Definition args_A128____addstate_avx2 : seq var_i :=
  [:: st_16461.(gv)
    ; AT_16462.(gv)
    ; buf_16463.(gv)
    ; offset_16464.(gv)
    ; _LEN_16465.(gv)
    ; _TRAILB_16466.(gv) ].
Definition tyout_A128____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A128____addstate_avx2 : seq var_i :=
  [:: st_16461.(gv); AT_16462.(gv); offset_16464.(gv) ].

(* Body *)
Definition body_A128____addstate_avx2 : cmd :=
  [:: cassgn (Lvar DELTA_16467.(gv)) (aint) (Pconst (0)%Z)
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pvar AT_16462) (Pconst (8)%Z))
        [:: ccall [:: Lvar DELTA_16467.(gv)
                    ; Lvar _LEN_16465.(gv)
                    ; Lvar _TRAILB_16466.(gv)
                    ; Lvar AT_16462.(gv)
                    ; Lvar r0_16468.(gv) ] A128____a_ilen_read_bcast_upto8_at [:: Pvar buf_16463
                                                                    ; Pvar offset_16464
                                                                    ; Pvar DELTA_16467
                                                                    ; Pvar _LEN_16465
                                                                    ; Pvar _TRAILB_16466
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_16462 ]
          ; cassgn (Laset Aligned AAscale U256 st_16461.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16461 (Pconst (0)%Z)) (Pvar r0_16468)) ]
        [::]
    ; cif
        (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_16462) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16465)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16466) (Pconst (0)%Z))))
        [:: ccall [:: Lvar DELTA_16467.(gv)
                    ; Lvar _LEN_16465.(gv)
                    ; Lvar _TRAILB_16466.(gv)
                    ; Lvar AT_16462.(gv)
                    ; Lvar r1_16469.(gv) ] A128____a_ilen_read_upto32_at [:: Pvar buf_16463
                                                                    ; Pvar offset_16464
                                                                    ; Pvar DELTA_16467
                                                                    ; Pvar _LEN_16465
                                                                    ; Pvar _TRAILB_16466
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_16462 ]
          ; cassgn (Laset Aligned AAscale U256 st_16461.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16461 (Pconst (1)%Z)) (Pvar r1_16469)) ]
        [::]
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16465)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16466) (Pconst (0)%Z)))
        [:: ccall [:: Lvar DELTA_16467.(gv)
                    ; Lvar _LEN_16465.(gv)
                    ; Lvar _TRAILB_16466.(gv)
                    ; Lvar AT_16462.(gv)
                    ; Lvar t64_2_16470.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_16463
                                                                    ; Pvar offset_16464
                                                                    ; Pvar DELTA_16467
                                                                    ; Pvar _LEN_16465
                                                                    ; Pvar _TRAILB_16466
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_16462 ]
          ; cassgn (Lvar t128_1_16471.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_16470))
          ; copn [:: Lvar t128_2_16472.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
          ; cif
              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16465)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16466) (Pconst (0)%Z)))
              [:: ccall [:: Lvar DELTA_16467.(gv)
                          ; Lvar _LEN_16465.(gv)
                          ; Lvar _TRAILB_16466.(gv)
                          ; Lvar AT_16462.(gv)
                          ; Lvar r3_16473.(gv) ] A128____a_ilen_read_upto32_at [:: Pvar buf_16463
                                                                    ; Pvar offset_16464
                                                                    ; Pvar DELTA_16467
                                                                    ; Pvar _LEN_16465
                                                                    ; Pvar _TRAILB_16466
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_16462 ]
                ; ccall [:: Lvar DELTA_16467.(gv)
                          ; Lvar _LEN_16465.(gv)
                          ; Lvar _TRAILB_16466.(gv)
                          ; Lvar AT_16462.(gv)
                          ; Lvar t64_3_16474.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_16463
                                                                    ; Pvar offset_16464
                                                                    ; Pvar DELTA_16467
                                                                    ; Pvar _LEN_16465
                                                                    ; Pvar _TRAILB_16466
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_16462 ]
                ; cassgn (Lvar t128_2_16472.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_16474))
                ; ccall [:: Lvar DELTA_16467.(gv)
                          ; Lvar _LEN_16465.(gv)
                          ; Lvar _TRAILB_16466.(gv)
                          ; Lvar AT_16462.(gv)
                          ; Lvar r4_16475.(gv) ] A128____a_ilen_read_upto32_at [:: Pvar buf_16463
                                                                    ; Pvar offset_16464
                                                                    ; Pvar DELTA_16467
                                                                    ; Pvar _LEN_16465
                                                                    ; Pvar _TRAILB_16466
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_16462 ]
                ; ccall [:: Lvar DELTA_16467.(gv)
                          ; Lvar _LEN_16465.(gv)
                          ; Lvar _TRAILB_16466.(gv)
                          ; Lvar AT_16462.(gv)
                          ; Lvar t64_4_16476.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_16463
                                                                    ; Pvar offset_16464
                                                                    ; Pvar DELTA_16467
                                                                    ; Pvar _LEN_16465
                                                                    ; Pvar _TRAILB_16466
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_16462 ]
                ; copn [:: Lvar t128_1_16471.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_16471
                                                                    ; Pvar t64_4_16476
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_16467.(gv)
                          ; Lvar _LEN_16465.(gv)
                          ; Lvar _TRAILB_16466.(gv)
                          ; Lvar AT_16462.(gv)
                          ; Lvar r5_16477.(gv) ] A128____a_ilen_read_upto32_at [:: Pvar buf_16463
                                                                    ; Pvar offset_16464
                                                                    ; Pvar DELTA_16467
                                                                    ; Pvar _LEN_16465
                                                                    ; Pvar _TRAILB_16466
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_16462 ]
                ; ccall [:: Lvar DELTA_16467.(gv)
                          ; Lvar _LEN_16465.(gv)
                          ; Lvar _TRAILB_16466.(gv)
                          ; Lvar AT_16462.(gv)
                          ; Lvar t64_5_16478.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_16463
                                                                    ; Pvar offset_16464
                                                                    ; Pvar DELTA_16467
                                                                    ; Pvar _LEN_16465
                                                                    ; Pvar _TRAILB_16466
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_16462 ]
                ; copn [:: Lvar t128_2_16472.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_16472
                                                                    ; Pvar t64_5_16478
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_16467.(gv)
                          ; Lvar _LEN_16465.(gv)
                          ; Lvar _TRAILB_16466.(gv)
                          ; Lvar AT_16462.(gv)
                          ; Lvar r6_16479.(gv) ] A128____a_ilen_read_upto32_at [:: Pvar buf_16463
                                                                    ; Pvar offset_16464
                                                                    ; Pvar DELTA_16467
                                                                    ; Pvar _LEN_16465
                                                                    ; Pvar _TRAILB_16466
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_16462 ]
                ; ccall [:: Lvar st_16461.(gv) ] __addstate_r3456_avx2 [:: Pvar st_16461
                                                                    ; Pvar r3_16473
                                                                    ; Pvar r4_16475
                                                                    ; Pvar r5_16477
                                                                    ; Pvar r6_16479 ] ]
              [::]
          ; cassgn (Lvar r2_16480.(gv)) (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_16472))
          ; copn [:: Lvar r2_16480.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_16480
                                                                    ; Pvar t128_1_16471
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Laset Aligned AAscale U256 st_16461.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16461 (Pconst (2)%Z)) (Pvar r2_16480)) ]
        [::]
    ; cassgn (Lvar offset_16464.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16464) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16467))) ].

Definition fd_A128____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____addstate_avx2;
    f_params := args_A128____addstate_avx2;
    f_body := body_A128____addstate_avx2;
    f_tyout := tyout_A128____addstate_avx2;
    f_res := res_A128____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
