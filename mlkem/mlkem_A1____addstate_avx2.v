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

(* A1____addstate_avx2 *)
(* Local variables *)
Definition st_18236 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 18236).
Definition AT_18237 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18237).
Definition buf_18238 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18238).
Definition offset_18239 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18239).
Definition _LEN_18240 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18240).
Definition _TRAILB_18241 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18241).
Definition DELTA_18242 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18242).
Definition r0_18243 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18243).
Definition r1_18244 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18244).
Definition t64_2_18245 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18245).
Definition t128_1_18246 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18246).
Definition t128_2_18247 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18247).
Definition r3_18248 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18248).
Definition t64_3_18249 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18249).
Definition r4_18250 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18250).
Definition t64_4_18251 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18251).
Definition r5_18252 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18252).
Definition t64_5_18253 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18253).
Definition r6_18254 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18254).
Definition r2_18255 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18255).

(* Signature *)
Definition tyin_A1____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1; aword U64; aint; aint ].
Definition args_A1____addstate_avx2 : seq var_i :=
  [:: st_18236.(gv)
    ; AT_18237.(gv)
    ; buf_18238.(gv)
    ; offset_18239.(gv)
    ; _LEN_18240.(gv)
    ; _TRAILB_18241.(gv) ].
Definition tyout_A1____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A1____addstate_avx2 : seq var_i :=
  [:: st_18236.(gv); AT_18237.(gv); offset_18239.(gv) ].

(* Body *)
Definition body_A1____addstate_avx2 : cmd :=
  [:: cassgn (Lvar DELTA_18242.(gv)) (aint) (Pconst (0)%Z)
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pvar AT_18237) (Pconst (8)%Z))
        [:: ccall [:: Lvar DELTA_18242.(gv)
                    ; Lvar _LEN_18240.(gv)
                    ; Lvar _TRAILB_18241.(gv)
                    ; Lvar AT_18237.(gv)
                    ; Lvar r0_18243.(gv) ] A1____a_ilen_read_bcast_upto8_at [:: Pvar buf_18238
                                                                    ; Pvar offset_18239
                                                                    ; Pvar DELTA_18242
                                                                    ; Pvar _LEN_18240
                                                                    ; Pvar _TRAILB_18241
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_18237 ]
          ; cassgn (Laset Aligned AAscale U256 st_18236.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_18236 (Pconst (0)%Z)) (Pvar r0_18243)) ]
        [::]
    ; cif
        (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_18237) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18240)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_18241) (Pconst (0)%Z))))
        [:: ccall [:: Lvar DELTA_18242.(gv)
                    ; Lvar _LEN_18240.(gv)
                    ; Lvar _TRAILB_18241.(gv)
                    ; Lvar AT_18237.(gv)
                    ; Lvar r1_18244.(gv) ] A1____a_ilen_read_upto32_at [:: Pvar buf_18238
                                                                    ; Pvar offset_18239
                                                                    ; Pvar DELTA_18242
                                                                    ; Pvar _LEN_18240
                                                                    ; Pvar _TRAILB_18241
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_18237 ]
          ; cassgn (Laset Aligned AAscale U256 st_18236.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_18236 (Pconst (1)%Z)) (Pvar r1_18244)) ]
        [::]
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18240)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_18241) (Pconst (0)%Z)))
        [:: ccall [:: Lvar DELTA_18242.(gv)
                    ; Lvar _LEN_18240.(gv)
                    ; Lvar _TRAILB_18241.(gv)
                    ; Lvar AT_18237.(gv)
                    ; Lvar t64_2_18245.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_18238
                                                                    ; Pvar offset_18239
                                                                    ; Pvar DELTA_18242
                                                                    ; Pvar _LEN_18240
                                                                    ; Pvar _TRAILB_18241
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_18237 ]
          ; cassgn (Lvar t128_1_18246.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_18245))
          ; copn [:: Lvar t128_2_18247.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
          ; cif
              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18240)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_18241) (Pconst (0)%Z)))
              [:: ccall [:: Lvar DELTA_18242.(gv)
                          ; Lvar _LEN_18240.(gv)
                          ; Lvar _TRAILB_18241.(gv)
                          ; Lvar AT_18237.(gv)
                          ; Lvar r3_18248.(gv) ] A1____a_ilen_read_upto32_at [:: Pvar buf_18238
                                                                    ; Pvar offset_18239
                                                                    ; Pvar DELTA_18242
                                                                    ; Pvar _LEN_18240
                                                                    ; Pvar _TRAILB_18241
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_18237 ]
                ; ccall [:: Lvar DELTA_18242.(gv)
                          ; Lvar _LEN_18240.(gv)
                          ; Lvar _TRAILB_18241.(gv)
                          ; Lvar AT_18237.(gv)
                          ; Lvar t64_3_18249.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_18238
                                                                    ; Pvar offset_18239
                                                                    ; Pvar DELTA_18242
                                                                    ; Pvar _LEN_18240
                                                                    ; Pvar _TRAILB_18241
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_18237 ]
                ; cassgn (Lvar t128_2_18247.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_18249))
                ; ccall [:: Lvar DELTA_18242.(gv)
                          ; Lvar _LEN_18240.(gv)
                          ; Lvar _TRAILB_18241.(gv)
                          ; Lvar AT_18237.(gv)
                          ; Lvar r4_18250.(gv) ] A1____a_ilen_read_upto32_at [:: Pvar buf_18238
                                                                    ; Pvar offset_18239
                                                                    ; Pvar DELTA_18242
                                                                    ; Pvar _LEN_18240
                                                                    ; Pvar _TRAILB_18241
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_18237 ]
                ; ccall [:: Lvar DELTA_18242.(gv)
                          ; Lvar _LEN_18240.(gv)
                          ; Lvar _TRAILB_18241.(gv)
                          ; Lvar AT_18237.(gv)
                          ; Lvar t64_4_18251.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_18238
                                                                    ; Pvar offset_18239
                                                                    ; Pvar DELTA_18242
                                                                    ; Pvar _LEN_18240
                                                                    ; Pvar _TRAILB_18241
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_18237 ]
                ; copn [:: Lvar t128_1_18246.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_18246
                                                                    ; Pvar t64_4_18251
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_18242.(gv)
                          ; Lvar _LEN_18240.(gv)
                          ; Lvar _TRAILB_18241.(gv)
                          ; Lvar AT_18237.(gv)
                          ; Lvar r5_18252.(gv) ] A1____a_ilen_read_upto32_at [:: Pvar buf_18238
                                                                    ; Pvar offset_18239
                                                                    ; Pvar DELTA_18242
                                                                    ; Pvar _LEN_18240
                                                                    ; Pvar _TRAILB_18241
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_18237 ]
                ; ccall [:: Lvar DELTA_18242.(gv)
                          ; Lvar _LEN_18240.(gv)
                          ; Lvar _TRAILB_18241.(gv)
                          ; Lvar AT_18237.(gv)
                          ; Lvar t64_5_18253.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_18238
                                                                    ; Pvar offset_18239
                                                                    ; Pvar DELTA_18242
                                                                    ; Pvar _LEN_18240
                                                                    ; Pvar _TRAILB_18241
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_18237 ]
                ; copn [:: Lvar t128_2_18247.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_18247
                                                                    ; Pvar t64_5_18253
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_18242.(gv)
                          ; Lvar _LEN_18240.(gv)
                          ; Lvar _TRAILB_18241.(gv)
                          ; Lvar AT_18237.(gv)
                          ; Lvar r6_18254.(gv) ] A1____a_ilen_read_upto32_at [:: Pvar buf_18238
                                                                    ; Pvar offset_18239
                                                                    ; Pvar DELTA_18242
                                                                    ; Pvar _LEN_18240
                                                                    ; Pvar _TRAILB_18241
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_18237 ]
                ; ccall [:: Lvar st_18236.(gv) ] __addstate_r3456_avx2 [:: Pvar st_18236
                                                                    ; Pvar r3_18248
                                                                    ; Pvar r4_18250
                                                                    ; Pvar r5_18252
                                                                    ; Pvar r6_18254 ] ]
              [::]
          ; cassgn (Lvar r2_18255.(gv)) (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_18247))
          ; copn [:: Lvar r2_18255.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_18255
                                                                    ; Pvar t128_1_18246
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Laset Aligned AAscale U256 st_18236.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_18236 (Pconst (2)%Z)) (Pvar r2_18255)) ]
        [::]
    ; cassgn (Lvar offset_18239.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18239) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18242))) ].

Definition fd_A1____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____addstate_avx2;
    f_params := args_A1____addstate_avx2;
    f_body := body_A1____addstate_avx2;
    f_tyout := tyout_A1____addstate_avx2;
    f_res := res_A1____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
