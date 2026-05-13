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

(* A1184____addstate_avx2 *)
(* Local variables *)
Definition st_16079 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16079).
Definition AT_16080 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16080).
Definition buf_16081 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16081).
Definition offset_16082 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16082).
Definition _LEN_16083 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16083).
Definition _TRAILB_16084 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16084).
Definition DELTA_16085 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16085).
Definition r0_16086 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16086).
Definition r1_16087 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16087).
Definition t64_2_16088 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16088).
Definition t128_1_16089 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16089).
Definition t128_2_16090 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16090).
Definition r3_16091 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16091).
Definition t64_3_16092 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16092).
Definition r4_16093 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16093).
Definition t64_4_16094 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16094).
Definition r5_16095 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16095).
Definition t64_5_16096 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16096).
Definition r6_16097 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16097).
Definition r2_16098 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16098).

(* Signature *)
Definition tyin_A1184____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1184; aword U64; aint; aint ].
Definition args_A1184____addstate_avx2 : seq var_i :=
  [:: st_16079.(gv)
    ; AT_16080.(gv)
    ; buf_16081.(gv)
    ; offset_16082.(gv)
    ; _LEN_16083.(gv)
    ; _TRAILB_16084.(gv) ].
Definition tyout_A1184____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A1184____addstate_avx2 : seq var_i :=
  [:: st_16079.(gv); AT_16080.(gv); offset_16082.(gv) ].

(* Body *)
Definition body_A1184____addstate_avx2 : cmd :=
  [:: cassgn (Lvar DELTA_16085.(gv)) (aint) (Pconst (0)%Z)
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pvar AT_16080) (Pconst (8)%Z))
        [:: ccall [:: Lvar DELTA_16085.(gv)
                    ; Lvar _LEN_16083.(gv)
                    ; Lvar _TRAILB_16084.(gv)
                    ; Lvar AT_16080.(gv)
                    ; Lvar r0_16086.(gv) ] A1184____a_ilen_read_bcast_upto8_at [:: Pvar buf_16081
                                                                    ; Pvar offset_16082
                                                                    ; Pvar DELTA_16085
                                                                    ; Pvar _LEN_16083
                                                                    ; Pvar _TRAILB_16084
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_16080 ]
          ; cassgn (Laset Aligned AAscale U256 st_16079.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16079 (Pconst (0)%Z)) (Pvar r0_16086)) ]
        [::]
    ; cif
        (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_16080) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16083)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16084) (Pconst (0)%Z))))
        [:: ccall [:: Lvar DELTA_16085.(gv)
                    ; Lvar _LEN_16083.(gv)
                    ; Lvar _TRAILB_16084.(gv)
                    ; Lvar AT_16080.(gv)
                    ; Lvar r1_16087.(gv) ] A1184____a_ilen_read_upto32_at [:: Pvar buf_16081
                                                                    ; Pvar offset_16082
                                                                    ; Pvar DELTA_16085
                                                                    ; Pvar _LEN_16083
                                                                    ; Pvar _TRAILB_16084
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_16080 ]
          ; cassgn (Laset Aligned AAscale U256 st_16079.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16079 (Pconst (1)%Z)) (Pvar r1_16087)) ]
        [::]
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16083)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16084) (Pconst (0)%Z)))
        [:: ccall [:: Lvar DELTA_16085.(gv)
                    ; Lvar _LEN_16083.(gv)
                    ; Lvar _TRAILB_16084.(gv)
                    ; Lvar AT_16080.(gv)
                    ; Lvar t64_2_16088.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_16081
                                                                    ; Pvar offset_16082
                                                                    ; Pvar DELTA_16085
                                                                    ; Pvar _LEN_16083
                                                                    ; Pvar _TRAILB_16084
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_16080 ]
          ; cassgn (Lvar t128_1_16089.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_16088))
          ; copn [:: Lvar t128_2_16090.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
          ; cif
              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16083)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16084) (Pconst (0)%Z)))
              [:: ccall [:: Lvar DELTA_16085.(gv)
                          ; Lvar _LEN_16083.(gv)
                          ; Lvar _TRAILB_16084.(gv)
                          ; Lvar AT_16080.(gv)
                          ; Lvar r3_16091.(gv) ] A1184____a_ilen_read_upto32_at [:: Pvar buf_16081
                                                                    ; Pvar offset_16082
                                                                    ; Pvar DELTA_16085
                                                                    ; Pvar _LEN_16083
                                                                    ; Pvar _TRAILB_16084
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_16080 ]
                ; ccall [:: Lvar DELTA_16085.(gv)
                          ; Lvar _LEN_16083.(gv)
                          ; Lvar _TRAILB_16084.(gv)
                          ; Lvar AT_16080.(gv)
                          ; Lvar t64_3_16092.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_16081
                                                                    ; Pvar offset_16082
                                                                    ; Pvar DELTA_16085
                                                                    ; Pvar _LEN_16083
                                                                    ; Pvar _TRAILB_16084
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_16080 ]
                ; cassgn (Lvar t128_2_16090.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_16092))
                ; ccall [:: Lvar DELTA_16085.(gv)
                          ; Lvar _LEN_16083.(gv)
                          ; Lvar _TRAILB_16084.(gv)
                          ; Lvar AT_16080.(gv)
                          ; Lvar r4_16093.(gv) ] A1184____a_ilen_read_upto32_at [:: Pvar buf_16081
                                                                    ; Pvar offset_16082
                                                                    ; Pvar DELTA_16085
                                                                    ; Pvar _LEN_16083
                                                                    ; Pvar _TRAILB_16084
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_16080 ]
                ; ccall [:: Lvar DELTA_16085.(gv)
                          ; Lvar _LEN_16083.(gv)
                          ; Lvar _TRAILB_16084.(gv)
                          ; Lvar AT_16080.(gv)
                          ; Lvar t64_4_16094.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_16081
                                                                    ; Pvar offset_16082
                                                                    ; Pvar DELTA_16085
                                                                    ; Pvar _LEN_16083
                                                                    ; Pvar _TRAILB_16084
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_16080 ]
                ; copn [:: Lvar t128_1_16089.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_16089
                                                                    ; Pvar t64_4_16094
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_16085.(gv)
                          ; Lvar _LEN_16083.(gv)
                          ; Lvar _TRAILB_16084.(gv)
                          ; Lvar AT_16080.(gv)
                          ; Lvar r5_16095.(gv) ] A1184____a_ilen_read_upto32_at [:: Pvar buf_16081
                                                                    ; Pvar offset_16082
                                                                    ; Pvar DELTA_16085
                                                                    ; Pvar _LEN_16083
                                                                    ; Pvar _TRAILB_16084
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_16080 ]
                ; ccall [:: Lvar DELTA_16085.(gv)
                          ; Lvar _LEN_16083.(gv)
                          ; Lvar _TRAILB_16084.(gv)
                          ; Lvar AT_16080.(gv)
                          ; Lvar t64_5_16096.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_16081
                                                                    ; Pvar offset_16082
                                                                    ; Pvar DELTA_16085
                                                                    ; Pvar _LEN_16083
                                                                    ; Pvar _TRAILB_16084
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_16080 ]
                ; copn [:: Lvar t128_2_16090.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_16090
                                                                    ; Pvar t64_5_16096
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_16085.(gv)
                          ; Lvar _LEN_16083.(gv)
                          ; Lvar _TRAILB_16084.(gv)
                          ; Lvar AT_16080.(gv)
                          ; Lvar r6_16097.(gv) ] A1184____a_ilen_read_upto32_at [:: Pvar buf_16081
                                                                    ; Pvar offset_16082
                                                                    ; Pvar DELTA_16085
                                                                    ; Pvar _LEN_16083
                                                                    ; Pvar _TRAILB_16084
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_16080 ]
                ; ccall [:: Lvar st_16079.(gv) ] __addstate_r3456_avx2 [:: Pvar st_16079
                                                                    ; Pvar r3_16091
                                                                    ; Pvar r4_16093
                                                                    ; Pvar r5_16095
                                                                    ; Pvar r6_16097 ] ]
              [::]
          ; cassgn (Lvar r2_16098.(gv)) (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_16090))
          ; copn [:: Lvar r2_16098.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_16098
                                                                    ; Pvar t128_1_16089
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Laset Aligned AAscale U256 st_16079.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16079 (Pconst (2)%Z)) (Pvar r2_16098)) ]
        [::]
    ; cassgn (Lvar offset_16082.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16082) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16085))) ].

Definition fd_A1184____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____addstate_avx2;
    f_params := args_A1184____addstate_avx2;
    f_body := body_A1184____addstate_avx2;
    f_tyout := tyout_A1184____addstate_avx2;
    f_res := res_A1184____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
