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

(* __addstate_m_avx2 *)
(* Local variables *)
Definition st_18795 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 18795).
Definition AT_18796 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18796).
Definition buf_18797 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18797).
Definition _LEN : gvar := mk_rocq_gvar Slocal (aint) (mkident 18798).
Definition _TRAILB : gvar := mk_rocq_gvar Slocal (aint) (mkident 18799).
Definition r0_18800 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18800).
Definition r1_18801 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18801).
Definition t64_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18802).
Definition t128_1_18803 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18803).
Definition t128_2 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18804).
Definition r3_18805 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18805).
Definition t64_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18806).
Definition r4_18807 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18807).
Definition t64_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18808).
Definition r5_18809 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18809).
Definition t64_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18810).
Definition r6_18811 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18811).
Definition r2_18812 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18812).

(* Signature *)
Definition tyin___addstate_m_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64; aint; aint ].
Definition args___addstate_m_avx2 : seq var_i :=
  [:: st_18795.(gv); AT_18796.(gv); buf_18797.(gv); _LEN.(gv); _TRAILB.(gv) ].
Definition tyout___addstate_m_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res___addstate_m_avx2 : seq var_i :=
  [:: st_18795.(gv); AT_18796.(gv); buf_18797.(gv) ].

(* Body *)
Definition body___addstate_m_avx2 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pvar AT_18796) (Pconst (8)%Z))
        [:: ccall [:: Lvar buf_18797.(gv)
                    ; Lvar _LEN.(gv)
                    ; Lvar _TRAILB.(gv)
                    ; Lvar AT_18796.(gv)
                    ; Lvar r0_18800.(gv) ] __m_ilen_read_bcast_upto8_at [:: Pvar buf_18797
                                                                    ; Pvar _LEN
                                                                    ; Pvar _TRAILB
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_18796 ]
          ; cassgn (Laset Aligned AAscale U256 st_18795.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_18795 (Pconst (0)%Z)) (Pvar r0_18800)) ]
        [::]
    ; cif
        (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_18796) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB) (Pconst (0)%Z))))
        [:: ccall [:: Lvar buf_18797.(gv)
                    ; Lvar _LEN.(gv)
                    ; Lvar _TRAILB.(gv)
                    ; Lvar AT_18796.(gv)
                    ; Lvar r1_18801.(gv) ] __m_ilen_read_upto32_at [:: Pvar buf_18797
                                                                    ; Pvar _LEN
                                                                    ; Pvar _TRAILB
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_18796 ]
          ; cassgn (Laset Aligned AAscale U256 st_18795.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_18795 (Pconst (1)%Z)) (Pvar r1_18801)) ]
        [::]
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB) (Pconst (0)%Z)))
        [:: ccall [:: Lvar buf_18797.(gv)
                    ; Lvar _LEN.(gv)
                    ; Lvar _TRAILB.(gv)
                    ; Lvar AT_18796.(gv)
                    ; Lvar t64_2.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf_18797
                                                                 ; Pvar _LEN
                                                                 ; Pvar _TRAILB
                                                                 ; Pconst (40)%Z
                                                                 ; Pvar AT_18796 ]
          ; cassgn (Lvar t128_1_18803.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2))
          ; copn [:: Lvar t128_2.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
          ; cif
              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB) (Pconst (0)%Z)))
              [:: ccall [:: Lvar buf_18797.(gv)
                          ; Lvar _LEN.(gv)
                          ; Lvar _TRAILB.(gv)
                          ; Lvar AT_18796.(gv)
                          ; Lvar r3_18805.(gv) ] __m_ilen_read_upto32_at [:: Pvar buf_18797
                                                                    ; Pvar _LEN
                                                                    ; Pvar _TRAILB
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_18796 ]
                ; ccall [:: Lvar buf_18797.(gv)
                          ; Lvar _LEN.(gv)
                          ; Lvar _TRAILB.(gv)
                          ; Lvar AT_18796.(gv)
                          ; Lvar t64_3.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf_18797
                                                                    ; Pvar _LEN
                                                                    ; Pvar _TRAILB
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_18796 ]
                ; cassgn (Lvar t128_2.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3))
                ; ccall [:: Lvar buf_18797.(gv)
                          ; Lvar _LEN.(gv)
                          ; Lvar _TRAILB.(gv)
                          ; Lvar AT_18796.(gv)
                          ; Lvar r4_18807.(gv) ] __m_ilen_read_upto32_at [:: Pvar buf_18797
                                                                    ; Pvar _LEN
                                                                    ; Pvar _TRAILB
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_18796 ]
                ; ccall [:: Lvar buf_18797.(gv)
                          ; Lvar _LEN.(gv)
                          ; Lvar _TRAILB.(gv)
                          ; Lvar AT_18796.(gv)
                          ; Lvar t64_4.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf_18797
                                                                    ; Pvar _LEN
                                                                    ; Pvar _TRAILB
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_18796 ]
                ; copn [:: Lvar t128_1_18803.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_18803
                                                                    ; Pvar t64_4
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar buf_18797.(gv)
                          ; Lvar _LEN.(gv)
                          ; Lvar _TRAILB.(gv)
                          ; Lvar AT_18796.(gv)
                          ; Lvar r5_18809.(gv) ] __m_ilen_read_upto32_at [:: Pvar buf_18797
                                                                    ; Pvar _LEN
                                                                    ; Pvar _TRAILB
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_18796 ]
                ; ccall [:: Lvar buf_18797.(gv)
                          ; Lvar _LEN.(gv)
                          ; Lvar _TRAILB.(gv)
                          ; Lvar AT_18796.(gv)
                          ; Lvar t64_5.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf_18797
                                                                    ; Pvar _LEN
                                                                    ; Pvar _TRAILB
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_18796 ]
                ; copn [:: Lvar t128_2.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2
                                                                    ; Pvar t64_5
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
                ; ccall [:: Lvar buf_18797.(gv)
                          ; Lvar _LEN.(gv)
                          ; Lvar _TRAILB.(gv)
                          ; Lvar AT_18796.(gv)
                          ; Lvar r6_18811.(gv) ] __m_ilen_read_upto32_at [:: Pvar buf_18797
                                                                    ; Pvar _LEN
                                                                    ; Pvar _TRAILB
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_18796 ]
                ; ccall [:: Lvar st_18795.(gv) ] __addstate_r3456_avx2 [:: Pvar st_18795
                                                                    ; Pvar r3_18805
                                                                    ; Pvar r4_18807
                                                                    ; Pvar r5_18809
                                                                    ; Pvar r6_18811 ] ]
              [::]
          ; cassgn (Lvar r2_18812.(gv)) (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2))
          ; copn [:: Lvar r2_18812.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_18812
                                                                    ; Pvar t128_1_18803
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Laset Aligned AAscale U256 st_18795.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_18795 (Pconst (2)%Z)) (Pvar r2_18812)) ]
        [::] ].

Definition fd___addstate_m_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___addstate_m_avx2;
    f_params := args___addstate_m_avx2;
    f_body := body___addstate_m_avx2;
    f_tyout := tyout___addstate_m_avx2;
    f_res := res___addstate_m_avx2;
    f_extra := tt;
  |}.

End IDO.
