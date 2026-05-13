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

(* A1120____addstate_avx2 *)
(* Local variables *)
Definition st_15315 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 15315).
Definition AT_15316 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15316).
Definition buf_15317 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15317).
Definition offset_15318 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15318).
Definition _LEN_15319 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15319).
Definition _TRAILB_15320 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15320).
Definition DELTA_15321 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15321).
Definition r0_15322 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15322).
Definition r1_15323 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15323).
Definition t64_2_15324 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15324).
Definition t128_1_15325 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15325).
Definition t128_2_15326 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15326).
Definition r3_15327 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15327).
Definition t64_3_15328 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15328).
Definition r4_15329 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15329).
Definition t64_4_15330 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15330).
Definition r5_15331 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15331).
Definition t64_5_15332 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15332).
Definition r6_15333 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15333).
Definition r2_15334 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15334).

(* Signature *)
Definition tyin_A1120____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1120; aword U64; aint; aint ].
Definition args_A1120____addstate_avx2 : seq var_i :=
  [:: st_15315.(gv)
    ; AT_15316.(gv)
    ; buf_15317.(gv)
    ; offset_15318.(gv)
    ; _LEN_15319.(gv)
    ; _TRAILB_15320.(gv) ].
Definition tyout_A1120____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A1120____addstate_avx2 : seq var_i :=
  [:: st_15315.(gv); AT_15316.(gv); offset_15318.(gv) ].

(* Body *)
Definition body_A1120____addstate_avx2 : cmd :=
  [:: cassgn (Lvar DELTA_15321.(gv)) (aint) (Pconst (0)%Z)
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pvar AT_15316) (Pconst (8)%Z))
        [:: ccall [:: Lvar DELTA_15321.(gv)
                    ; Lvar _LEN_15319.(gv)
                    ; Lvar _TRAILB_15320.(gv)
                    ; Lvar AT_15316.(gv)
                    ; Lvar r0_15322.(gv) ] A1120____a_ilen_read_bcast_upto8_at [:: Pvar buf_15317
                                                                    ; Pvar offset_15318
                                                                    ; Pvar DELTA_15321
                                                                    ; Pvar _LEN_15319
                                                                    ; Pvar _TRAILB_15320
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_15316 ]
          ; cassgn (Laset Aligned AAscale U256 st_15315.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_15315 (Pconst (0)%Z)) (Pvar r0_15322)) ]
        [::]
    ; cif
        (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_15316) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15319)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_15320) (Pconst (0)%Z))))
        [:: ccall [:: Lvar DELTA_15321.(gv)
                    ; Lvar _LEN_15319.(gv)
                    ; Lvar _TRAILB_15320.(gv)
                    ; Lvar AT_15316.(gv)
                    ; Lvar r1_15323.(gv) ] A1120____a_ilen_read_upto32_at [:: Pvar buf_15317
                                                                    ; Pvar offset_15318
                                                                    ; Pvar DELTA_15321
                                                                    ; Pvar _LEN_15319
                                                                    ; Pvar _TRAILB_15320
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_15316 ]
          ; cassgn (Laset Aligned AAscale U256 st_15315.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_15315 (Pconst (1)%Z)) (Pvar r1_15323)) ]
        [::]
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15319)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_15320) (Pconst (0)%Z)))
        [:: ccall [:: Lvar DELTA_15321.(gv)
                    ; Lvar _LEN_15319.(gv)
                    ; Lvar _TRAILB_15320.(gv)
                    ; Lvar AT_15316.(gv)
                    ; Lvar t64_2_15324.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_15317
                                                                    ; Pvar offset_15318
                                                                    ; Pvar DELTA_15321
                                                                    ; Pvar _LEN_15319
                                                                    ; Pvar _TRAILB_15320
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_15316 ]
          ; cassgn (Lvar t128_1_15325.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_15324))
          ; copn [:: Lvar t128_2_15326.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
          ; cif
              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15319)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_15320) (Pconst (0)%Z)))
              [:: ccall [:: Lvar DELTA_15321.(gv)
                          ; Lvar _LEN_15319.(gv)
                          ; Lvar _TRAILB_15320.(gv)
                          ; Lvar AT_15316.(gv)
                          ; Lvar r3_15327.(gv) ] A1120____a_ilen_read_upto32_at [:: Pvar buf_15317
                                                                    ; Pvar offset_15318
                                                                    ; Pvar DELTA_15321
                                                                    ; Pvar _LEN_15319
                                                                    ; Pvar _TRAILB_15320
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_15316 ]
                ; ccall [:: Lvar DELTA_15321.(gv)
                          ; Lvar _LEN_15319.(gv)
                          ; Lvar _TRAILB_15320.(gv)
                          ; Lvar AT_15316.(gv)
                          ; Lvar t64_3_15328.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_15317
                                                                    ; Pvar offset_15318
                                                                    ; Pvar DELTA_15321
                                                                    ; Pvar _LEN_15319
                                                                    ; Pvar _TRAILB_15320
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_15316 ]
                ; cassgn (Lvar t128_2_15326.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_15328))
                ; ccall [:: Lvar DELTA_15321.(gv)
                          ; Lvar _LEN_15319.(gv)
                          ; Lvar _TRAILB_15320.(gv)
                          ; Lvar AT_15316.(gv)
                          ; Lvar r4_15329.(gv) ] A1120____a_ilen_read_upto32_at [:: Pvar buf_15317
                                                                    ; Pvar offset_15318
                                                                    ; Pvar DELTA_15321
                                                                    ; Pvar _LEN_15319
                                                                    ; Pvar _TRAILB_15320
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_15316 ]
                ; ccall [:: Lvar DELTA_15321.(gv)
                          ; Lvar _LEN_15319.(gv)
                          ; Lvar _TRAILB_15320.(gv)
                          ; Lvar AT_15316.(gv)
                          ; Lvar t64_4_15330.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_15317
                                                                    ; Pvar offset_15318
                                                                    ; Pvar DELTA_15321
                                                                    ; Pvar _LEN_15319
                                                                    ; Pvar _TRAILB_15320
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_15316 ]
                ; copn [:: Lvar t128_1_15325.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_15325
                                                                    ; Pvar t64_4_15330
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_15321.(gv)
                          ; Lvar _LEN_15319.(gv)
                          ; Lvar _TRAILB_15320.(gv)
                          ; Lvar AT_15316.(gv)
                          ; Lvar r5_15331.(gv) ] A1120____a_ilen_read_upto32_at [:: Pvar buf_15317
                                                                    ; Pvar offset_15318
                                                                    ; Pvar DELTA_15321
                                                                    ; Pvar _LEN_15319
                                                                    ; Pvar _TRAILB_15320
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_15316 ]
                ; ccall [:: Lvar DELTA_15321.(gv)
                          ; Lvar _LEN_15319.(gv)
                          ; Lvar _TRAILB_15320.(gv)
                          ; Lvar AT_15316.(gv)
                          ; Lvar t64_5_15332.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_15317
                                                                    ; Pvar offset_15318
                                                                    ; Pvar DELTA_15321
                                                                    ; Pvar _LEN_15319
                                                                    ; Pvar _TRAILB_15320
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_15316 ]
                ; copn [:: Lvar t128_2_15326.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_15326
                                                                    ; Pvar t64_5_15332
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_15321.(gv)
                          ; Lvar _LEN_15319.(gv)
                          ; Lvar _TRAILB_15320.(gv)
                          ; Lvar AT_15316.(gv)
                          ; Lvar r6_15333.(gv) ] A1120____a_ilen_read_upto32_at [:: Pvar buf_15317
                                                                    ; Pvar offset_15318
                                                                    ; Pvar DELTA_15321
                                                                    ; Pvar _LEN_15319
                                                                    ; Pvar _TRAILB_15320
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_15316 ]
                ; ccall [:: Lvar st_15315.(gv) ] __addstate_r3456_avx2 [:: Pvar st_15315
                                                                    ; Pvar r3_15327
                                                                    ; Pvar r4_15329
                                                                    ; Pvar r5_15331
                                                                    ; Pvar r6_15333 ] ]
              [::]
          ; cassgn (Lvar r2_15334.(gv)) (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_15326))
          ; copn [:: Lvar r2_15334.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_15334
                                                                    ; Pvar t128_1_15325
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Laset Aligned AAscale U256 st_15315.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_15315 (Pconst (2)%Z)) (Pvar r2_15334)) ]
        [::]
    ; cassgn (Lvar offset_15318.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15318) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15321))) ].

Definition fd_A1120____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____addstate_avx2;
    f_params := args_A1120____addstate_avx2;
    f_body := body_A1120____addstate_avx2;
    f_tyout := tyout_A1120____addstate_avx2;
    f_res := res_A1120____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
