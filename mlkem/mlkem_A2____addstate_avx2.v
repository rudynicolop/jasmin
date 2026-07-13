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

(* A2____addstate_avx2 *)
(* Local variables *)
Definition st_26 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 17854).
Definition AT_23 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17855).
Definition buf_36 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17856).
Definition offset_23 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17857).
Definition _LEN_19 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17858).
Definition _TRAILB_11 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17859).
Definition DELTA_17 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17860).
Definition r0_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17861).
Definition r1_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17862).
Definition t64_2_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17863).
Definition t128_1_8 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17864).
Definition t128_2_1 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17865).
Definition r3_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17866).
Definition t64_3_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17867).
Definition r4_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17868).
Definition t64_4_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17869).
Definition r5_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17870).
Definition t64_5_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17871).
Definition r6_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17872).
Definition r2_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17873).

(* Signature *)
Definition tyin_A2____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 2; aword U64; aint; aint ].
Definition args_A2____addstate_avx2 : seq var_i :=
  [:: st_26.(gv)
    ; AT_23.(gv)
    ; buf_36.(gv)
    ; offset_23.(gv)
    ; _LEN_19.(gv)
    ; _TRAILB_11.(gv) ].
Definition tyout_A2____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A2____addstate_avx2 : seq var_i :=
  [:: st_26.(gv); AT_23.(gv); offset_23.(gv) ].

(* Body *)
Definition body_A2____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_17.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_23) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17.(gv)
                                                                ; Lvar _LEN_19.(gv)
                                                                ; Lvar _TRAILB_11.(gv)
                                                                ; Lvar AT_23.(gv)
                                                                ; Lvar r0_6.(gv) ] A2____a_ilen_read_bcast_upto8_at [:: Pvar buf_36
                                                                    ; Pvar offset_23
                                                                    ; Pvar DELTA_17
                                                                    ; Pvar _LEN_19
                                                                    ; Pvar _TRAILB_11
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_23 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_26.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_26 (Pconst (0)%Z)) (Pvar r0_6))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_23) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_19)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_11) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17.(gv)
                                                                ; Lvar _LEN_19.(gv)
                                                                ; Lvar _TRAILB_11.(gv)
                                                                ; Lvar AT_23.(gv)
                                                                ; Lvar r1_6.(gv) ] A2____a_ilen_read_upto32_at [:: Pvar buf_36
                                                                    ; Pvar offset_23
                                                                    ; Pvar DELTA_17
                                                                    ; Pvar _LEN_19
                                                                    ; Pvar _TRAILB_11
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_23 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_26.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_26 (Pconst (1)%Z)) (Pvar r1_6))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_19)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_11) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17.(gv)
                                                                ; Lvar _LEN_19.(gv)
                                                                ; Lvar _TRAILB_11.(gv)
                                                                ; Lvar AT_23.(gv)
                                                                ; Lvar t64_2_1.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_36
                                                                    ; Pvar offset_23
                                                                    ; Pvar DELTA_17
                                                                    ; Pvar _LEN_19
                                                                    ; Pvar _TRAILB_11
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_23 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_8.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_1)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_1.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_19)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_11) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17.(gv)
                                                                  ; Lvar _LEN_19.(gv)
                                                                  ; Lvar _TRAILB_11.(gv)
                                                                  ; Lvar AT_23.(gv)
                                                                  ; Lvar r3_6.(gv) ] A2____a_ilen_read_upto32_at [:: Pvar buf_36
                                                                    ; Pvar offset_23
                                                                    ; Pvar DELTA_17
                                                                    ; Pvar _LEN_19
                                                                    ; Pvar _TRAILB_11
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_23 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17.(gv)
                                                                  ; Lvar _LEN_19.(gv)
                                                                  ; Lvar _TRAILB_11.(gv)
                                                                  ; Lvar AT_23.(gv)
                                                                  ; Lvar t64_3_1.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_36
                                                                    ; Pvar offset_23
                                                                    ; Pvar DELTA_17
                                                                    ; Pvar _LEN_19
                                                                    ; Pvar _TRAILB_11
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_23 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_1.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_1)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17.(gv)
                                                                  ; Lvar _LEN_19.(gv)
                                                                  ; Lvar _TRAILB_11.(gv)
                                                                  ; Lvar AT_23.(gv)
                                                                  ; Lvar r4_6.(gv) ] A2____a_ilen_read_upto32_at [:: Pvar buf_36
                                                                    ; Pvar offset_23
                                                                    ; Pvar DELTA_17
                                                                    ; Pvar _LEN_19
                                                                    ; Pvar _TRAILB_11
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_23 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17.(gv)
                                                                  ; Lvar _LEN_19.(gv)
                                                                  ; Lvar _TRAILB_11.(gv)
                                                                  ; Lvar AT_23.(gv)
                                                                  ; Lvar t64_4_1.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_36
                                                                    ; Pvar offset_23
                                                                    ; Pvar DELTA_17
                                                                    ; Pvar _LEN_19
                                                                    ; Pvar _TRAILB_11
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_23 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_8
                                                                    ; Pvar t64_4_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17.(gv)
                                                                  ; Lvar _LEN_19.(gv)
                                                                  ; Lvar _TRAILB_11.(gv)
                                                                  ; Lvar AT_23.(gv)
                                                                  ; Lvar r5_6.(gv) ] A2____a_ilen_read_upto32_at [:: Pvar buf_36
                                                                    ; Pvar offset_23
                                                                    ; Pvar DELTA_17
                                                                    ; Pvar _LEN_19
                                                                    ; Pvar _TRAILB_11
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_23 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17.(gv)
                                                                  ; Lvar _LEN_19.(gv)
                                                                  ; Lvar _TRAILB_11.(gv)
                                                                  ; Lvar AT_23.(gv)
                                                                  ; Lvar t64_5_1.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_36
                                                                    ; Pvar offset_23
                                                                    ; Pvar DELTA_17
                                                                    ; Pvar _LEN_19
                                                                    ; Pvar _TRAILB_11
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_23 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_1
                                                                    ; Pvar t64_5_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17.(gv)
                                                                  ; Lvar _LEN_19.(gv)
                                                                  ; Lvar _TRAILB_11.(gv)
                                                                  ; Lvar AT_23.(gv)
                                                                  ; Lvar r6_6.(gv) ] A2____a_ilen_read_upto32_at [:: Pvar buf_36
                                                                    ; Pvar offset_23
                                                                    ; Pvar DELTA_17
                                                                    ; Pvar _LEN_19
                                                                    ; Pvar _TRAILB_11
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_23 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_26.(gv) ] __addstate_r3456_avx2 [:: Pvar st_26
                                                                    ; Pvar r3_6
                                                                    ; Pvar r4_6
                                                                    ; Pvar r5_6
                                                                    ; Pvar r6_6 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_3.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_1)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_3.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_3
                                                                    ; Pvar t128_1_8
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_26.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_26 (Pconst (2)%Z)) (Pvar r2_3))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_23.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_23) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17)))) ].

Definition fd_A2____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____addstate_avx2;
    f_params := args_A2____addstate_avx2;
    f_body := body_A2____addstate_avx2;
    f_tyout := tyout_A2____addstate_avx2;
    f_res := res_A2____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
