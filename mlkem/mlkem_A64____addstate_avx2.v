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

(* A64____addstate_avx2 *)
(* Local variables *)
Definition st_16708 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16708).
Definition AT_16709 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16709).
Definition buf_16710 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 16710).
Definition offset_16711 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16711).
Definition _LEN_16712 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16712).
Definition _TRAILB_16713 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16713).
Definition DELTA_16714 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16714).
Definition r0_16715 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16715).
Definition r1_16716 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16716).
Definition t64_2_16717 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16717).
Definition t128_1_16718 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16718).
Definition t128_2_16719 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16719).
Definition r3_16720 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16720).
Definition t64_3_16721 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16721).
Definition r4_16722 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16722).
Definition t64_4_16723 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16723).
Definition r5_16724 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16724).
Definition t64_5_16725 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16725).
Definition r6_16726 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16726).
Definition r2_16727 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16727).

(* Signature *)
Definition tyin_A64____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 64; aword U64; aint; aint ].
Definition args_A64____addstate_avx2 : seq var_i :=
  [:: st_16708.(gv)
    ; AT_16709.(gv)
    ; buf_16710.(gv)
    ; offset_16711.(gv)
    ; _LEN_16712.(gv)
    ; _TRAILB_16713.(gv) ].
Definition tyout_A64____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A64____addstate_avx2 : seq var_i :=
  [:: st_16708.(gv); AT_16709.(gv); offset_16711.(gv) ].

(* Body *)
Definition body_A64____addstate_avx2 : cmd :=
  [:: cassgn (Lvar DELTA_16714.(gv)) (aint) (Pconst (0)%Z)
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pvar AT_16709) (Pconst (8)%Z))
        [:: ccall [:: Lvar DELTA_16714.(gv)
                    ; Lvar _LEN_16712.(gv)
                    ; Lvar _TRAILB_16713.(gv)
                    ; Lvar AT_16709.(gv)
                    ; Lvar r0_16715.(gv) ] A64____a_ilen_read_bcast_upto8_at [:: Pvar buf_16710
                                                                    ; Pvar offset_16711
                                                                    ; Pvar DELTA_16714
                                                                    ; Pvar _LEN_16712
                                                                    ; Pvar _TRAILB_16713
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_16709 ]
          ; cassgn (Laset Aligned AAscale U256 st_16708.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16708 (Pconst (0)%Z)) (Pvar r0_16715)) ]
        [::]
    ; cif
        (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_16709) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16712)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16713) (Pconst (0)%Z))))
        [:: ccall [:: Lvar DELTA_16714.(gv)
                    ; Lvar _LEN_16712.(gv)
                    ; Lvar _TRAILB_16713.(gv)
                    ; Lvar AT_16709.(gv)
                    ; Lvar r1_16716.(gv) ] A64____a_ilen_read_upto32_at [:: Pvar buf_16710
                                                                    ; Pvar offset_16711
                                                                    ; Pvar DELTA_16714
                                                                    ; Pvar _LEN_16712
                                                                    ; Pvar _TRAILB_16713
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_16709 ]
          ; cassgn (Laset Aligned AAscale U256 st_16708.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16708 (Pconst (1)%Z)) (Pvar r1_16716)) ]
        [::]
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16712)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16713) (Pconst (0)%Z)))
        [:: ccall [:: Lvar DELTA_16714.(gv)
                    ; Lvar _LEN_16712.(gv)
                    ; Lvar _TRAILB_16713.(gv)
                    ; Lvar AT_16709.(gv)
                    ; Lvar t64_2_16717.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_16710
                                                                    ; Pvar offset_16711
                                                                    ; Pvar DELTA_16714
                                                                    ; Pvar _LEN_16712
                                                                    ; Pvar _TRAILB_16713
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_16709 ]
          ; cassgn (Lvar t128_1_16718.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_16717))
          ; copn [:: Lvar t128_2_16719.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
          ; cif
              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16712)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16713) (Pconst (0)%Z)))
              [:: ccall [:: Lvar DELTA_16714.(gv)
                          ; Lvar _LEN_16712.(gv)
                          ; Lvar _TRAILB_16713.(gv)
                          ; Lvar AT_16709.(gv)
                          ; Lvar r3_16720.(gv) ] A64____a_ilen_read_upto32_at [:: Pvar buf_16710
                                                                    ; Pvar offset_16711
                                                                    ; Pvar DELTA_16714
                                                                    ; Pvar _LEN_16712
                                                                    ; Pvar _TRAILB_16713
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_16709 ]
                ; ccall [:: Lvar DELTA_16714.(gv)
                          ; Lvar _LEN_16712.(gv)
                          ; Lvar _TRAILB_16713.(gv)
                          ; Lvar AT_16709.(gv)
                          ; Lvar t64_3_16721.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_16710
                                                                    ; Pvar offset_16711
                                                                    ; Pvar DELTA_16714
                                                                    ; Pvar _LEN_16712
                                                                    ; Pvar _TRAILB_16713
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_16709 ]
                ; cassgn (Lvar t128_2_16719.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_16721))
                ; ccall [:: Lvar DELTA_16714.(gv)
                          ; Lvar _LEN_16712.(gv)
                          ; Lvar _TRAILB_16713.(gv)
                          ; Lvar AT_16709.(gv)
                          ; Lvar r4_16722.(gv) ] A64____a_ilen_read_upto32_at [:: Pvar buf_16710
                                                                    ; Pvar offset_16711
                                                                    ; Pvar DELTA_16714
                                                                    ; Pvar _LEN_16712
                                                                    ; Pvar _TRAILB_16713
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_16709 ]
                ; ccall [:: Lvar DELTA_16714.(gv)
                          ; Lvar _LEN_16712.(gv)
                          ; Lvar _TRAILB_16713.(gv)
                          ; Lvar AT_16709.(gv)
                          ; Lvar t64_4_16723.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_16710
                                                                    ; Pvar offset_16711
                                                                    ; Pvar DELTA_16714
                                                                    ; Pvar _LEN_16712
                                                                    ; Pvar _TRAILB_16713
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_16709 ]
                ; copn [:: Lvar t128_1_16718.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_16718
                                                                    ; Pvar t64_4_16723
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_16714.(gv)
                          ; Lvar _LEN_16712.(gv)
                          ; Lvar _TRAILB_16713.(gv)
                          ; Lvar AT_16709.(gv)
                          ; Lvar r5_16724.(gv) ] A64____a_ilen_read_upto32_at [:: Pvar buf_16710
                                                                    ; Pvar offset_16711
                                                                    ; Pvar DELTA_16714
                                                                    ; Pvar _LEN_16712
                                                                    ; Pvar _TRAILB_16713
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_16709 ]
                ; ccall [:: Lvar DELTA_16714.(gv)
                          ; Lvar _LEN_16712.(gv)
                          ; Lvar _TRAILB_16713.(gv)
                          ; Lvar AT_16709.(gv)
                          ; Lvar t64_5_16725.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_16710
                                                                    ; Pvar offset_16711
                                                                    ; Pvar DELTA_16714
                                                                    ; Pvar _LEN_16712
                                                                    ; Pvar _TRAILB_16713
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_16709 ]
                ; copn [:: Lvar t128_2_16719.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_16719
                                                                    ; Pvar t64_5_16725
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar DELTA_16714.(gv)
                          ; Lvar _LEN_16712.(gv)
                          ; Lvar _TRAILB_16713.(gv)
                          ; Lvar AT_16709.(gv)
                          ; Lvar r6_16726.(gv) ] A64____a_ilen_read_upto32_at [:: Pvar buf_16710
                                                                    ; Pvar offset_16711
                                                                    ; Pvar DELTA_16714
                                                                    ; Pvar _LEN_16712
                                                                    ; Pvar _TRAILB_16713
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_16709 ]
                ; ccall [:: Lvar st_16708.(gv) ] __addstate_r3456_avx2 [:: Pvar st_16708
                                                                    ; Pvar r3_16720
                                                                    ; Pvar r4_16722
                                                                    ; Pvar r5_16724
                                                                    ; Pvar r6_16726 ] ]
              [::]
          ; cassgn (Lvar r2_16727.(gv)) (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_16719))
          ; copn [:: Lvar r2_16727.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_16727
                                                                    ; Pvar t128_1_16718
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Laset Aligned AAscale U256 st_16708.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16708 (Pconst (2)%Z)) (Pvar r2_16727)) ]
        [::]
    ; cassgn (Lvar offset_16711.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16711) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16714))) ].

Definition fd_A64____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____addstate_avx2;
    f_params := args_A64____addstate_avx2;
    f_body := body_A64____addstate_avx2;
    f_tyout := tyout_A64____addstate_avx2;
    f_res := res_A64____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
