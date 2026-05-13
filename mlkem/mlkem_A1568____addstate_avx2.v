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

(* A1568____addstate_avx2 *)
(* Local variables *)
Definition st_15697 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 15697).
Definition AT_15698 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15698).
Definition buf_15699 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15699).
Definition offset_15700 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15700).
Definition _LEN_15701 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15701).
Definition _TRAILB_15702 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15702).
Definition DELTA_15703 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15703).
Definition r0_15704 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15704).
Definition r1_15705 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15705).
Definition t64_2_15706 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15706).
Definition t128_1_15707 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15707).
Definition t128_2_15708 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15708).
Definition r3_15709 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15709).
Definition t64_3_15710 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15710).
Definition r4_15711 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15711).
Definition t64_4_15712 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15712).
Definition r5_15713 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15713).
Definition t64_5_15714 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15714).
Definition r6_15715 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15715).
Definition r2_15716 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15716).

(* Signature *)
Definition tyin_A1568____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1568; aword U64; aint; aint ].
Definition args_A1568____addstate_avx2 : seq var_i :=
  [:: st_15697.(gv)
    ; AT_15698.(gv)
    ; buf_15699.(gv)
    ; offset_15700.(gv)
    ; _LEN_15701.(gv)
    ; _TRAILB_15702.(gv) ].
Definition tyout_A1568____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A1568____addstate_avx2 : seq var_i :=
  [:: st_15697.(gv); AT_15698.(gv); offset_15700.(gv) ].

(* Body *)
Definition body_A1568____addstate_avx2 : cmd :=
  [:: cassgn (Lvar DELTA_15703.(gv)) (aint) (Pconst (0)%Z)
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pvar AT_15698) (Pconst (8)%Z))
        [:: ccall [:: Lvar DELTA_15703.(gv)
                    ; Lvar _LEN_15701.(gv)
                    ; Lvar _TRAILB_15702.(gv)
                    ; Lvar AT_15698.(gv)
                    ; Lvar r0_15704.(gv) ] A1568____a_ilen_read_bcast_upto8_at [:: Pvar buf_15699
                                                                    ; Pvar offset_15700
                                                                    ; Pvar DELTA_15703
                                                                    ; Pvar _LEN_15701
                                                                    ; Pvar _TRAILB_15702
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_15698 ]
          ; cassgn (Laset Aligned AAscale U256 st_15697.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_15697 (Pconst (0)%Z)) (Pvar r0_15704)) ]
        [::]
    ; cif
        (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_15698) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15701)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_15702) (Pconst (0)%Z))))
        [:: ccall [:: Lvar DELTA_15703.(gv)
                    ; Lvar _LEN_15701.(gv)
                    ; Lvar _TRAILB_15702.(gv)
                    ; Lvar AT_15698.(gv)
                    ; Lvar r1_15705.(gv) ] A1568____a_ilen_read_upto32_at [:: Pvar buf_15699
                                                                    ; Pvar offset_15700
                                                                    ; Pvar DELTA_15703
                                                                    ; Pvar _LEN_15701
                                                                    ; Pvar _TRAILB_15702
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_15698 ]
          ; cassgn (Laset Aligned AAscale U256 st_15697.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_15697 (Pconst (1)%Z)) (Pvar r1_15705)) ]
        [::]
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15701)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_15702) (Pconst (0)%Z)))
        [:: ccall [:: Lvar DELTA_15703.(gv)
                    ; Lvar _LEN_15701.(gv)
                    ; Lvar _TRAILB_15702.(gv)
                    ; Lvar AT_15698.(gv)
                    ; Lvar t64_2_15706.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_15699
                                                                    ; Pvar offset_15700
                                                                    ; Pvar DELTA_15703
                                                                    ; Pvar _LEN_15701
                                                                    ; Pvar _TRAILB_15702
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_15698 ]
          ; cassgn (Lvar t128_1_15707.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_15706))
          ; copn [:: Lvar t128_2_15708.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
          ; cif
              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15701)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_15702) (Pconst (0)%Z)))
              [:: ccall [:: Lvar DELTA_15703.(gv)
                          ; Lvar _LEN_15701.(gv)
                          ; Lvar _TRAILB_15702.(gv)
                          ; Lvar AT_15698.(gv)
                          ; Lvar r3_15709.(gv) ] A1568____a_ilen_read_upto32_at [:: Pvar buf_15699
                                                                    ; Pvar offset_15700
                                                                    ; Pvar DELTA_15703
                                                                    ; Pvar _LEN_15701
                                                                    ; Pvar _TRAILB_15702
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_15698 ]
                ; ccall [:: Lvar DELTA_15703.(gv)
                          ; Lvar _LEN_15701.(gv)
                          ; Lvar _TRAILB_15702.(gv)
                          ; Lvar AT_15698.(gv)
                          ; Lvar t64_3_15710.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_15699
                                                                    ; Pvar offset_15700
                                                                    ; Pvar DELTA_15703
                                                                    ; Pvar _LEN_15701
                                                                    ; Pvar _TRAILB_15702
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_15698 ]
                ; cassgn (Lvar t128_2_15708.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_15710))
                ; ccall [:: Lvar DELTA_15703.(gv)
                          ; Lvar _LEN_15701.(gv)
                          ; Lvar _TRAILB_15702.(gv)
                          ; Lvar AT_15698.(gv)
                          ; Lvar r4_15711.(gv) ] A1568____a_ilen_read_upto32_at [:: Pvar buf_15699
                                                                    ; Pvar offset_15700
                                                                    ; Pvar DELTA_15703
                                                                    ; Pvar _LEN_15701
                                                                    ; Pvar _TRAILB_15702
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_15698 ]
                ; ccall [:: Lvar DELTA_15703.(gv)
                          ; Lvar _LEN_15701.(gv)
                          ; Lvar _TRAILB_15702.(gv)
                          ; Lvar AT_15698.(gv)
                          ; Lvar t64_4_15712.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_15699
                                                                    ; Pvar offset_15700
                                                                    ; Pvar DELTA_15703
                                                                    ; Pvar _LEN_15701
                                                                    ; Pvar _TRAILB_15702
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_15698 ]
                ; copn [:: Lvar t128_1_15707.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_15707
                                                                    ; Pvar t64_4_15712
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_15703.(gv)
                          ; Lvar _LEN_15701.(gv)
                          ; Lvar _TRAILB_15702.(gv)
                          ; Lvar AT_15698.(gv)
                          ; Lvar r5_15713.(gv) ] A1568____a_ilen_read_upto32_at [:: Pvar buf_15699
                                                                    ; Pvar offset_15700
                                                                    ; Pvar DELTA_15703
                                                                    ; Pvar _LEN_15701
                                                                    ; Pvar _TRAILB_15702
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_15698 ]
                ; ccall [:: Lvar DELTA_15703.(gv)
                          ; Lvar _LEN_15701.(gv)
                          ; Lvar _TRAILB_15702.(gv)
                          ; Lvar AT_15698.(gv)
                          ; Lvar t64_5_15714.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_15699
                                                                    ; Pvar offset_15700
                                                                    ; Pvar DELTA_15703
                                                                    ; Pvar _LEN_15701
                                                                    ; Pvar _TRAILB_15702
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_15698 ]
                ; copn [:: Lvar t128_2_15708.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_15708
                                                                    ; Pvar t64_5_15714
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_15703.(gv)
                          ; Lvar _LEN_15701.(gv)
                          ; Lvar _TRAILB_15702.(gv)
                          ; Lvar AT_15698.(gv)
                          ; Lvar r6_15715.(gv) ] A1568____a_ilen_read_upto32_at [:: Pvar buf_15699
                                                                    ; Pvar offset_15700
                                                                    ; Pvar DELTA_15703
                                                                    ; Pvar _LEN_15701
                                                                    ; Pvar _TRAILB_15702
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_15698 ]
                ; ccall [:: Lvar st_15697.(gv) ] __addstate_r3456_avx2 [:: Pvar st_15697
                                                                    ; Pvar r3_15709
                                                                    ; Pvar r4_15711
                                                                    ; Pvar r5_15713
                                                                    ; Pvar r6_15715 ] ]
              [::]
          ; cassgn (Lvar r2_15716.(gv)) (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_15708))
          ; copn [:: Lvar r2_15716.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_15716
                                                                    ; Pvar t128_1_15707
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Laset Aligned AAscale U256 st_15697.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_15697 (Pconst (2)%Z)) (Pvar r2_15716)) ]
        [::]
    ; cassgn (Lvar offset_15700.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15700) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15703))) ].

Definition fd_A1568____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____addstate_avx2;
    f_params := args_A1568____addstate_avx2;
    f_body := body_A1568____addstate_avx2;
    f_tyout := tyout_A1568____addstate_avx2;
    f_res := res_A1568____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
