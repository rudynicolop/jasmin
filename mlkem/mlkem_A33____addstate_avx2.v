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

(* A33____addstate_avx2 *)
(* Local variables *)
Definition st_46 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 17090).
Definition AT_43 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17091).
Definition buf_64 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17092).
Definition offset_57 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17093).
Definition _LEN_39 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17094).
Definition _TRAILB_23 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17095).
Definition DELTA_39 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17096).
Definition r0_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17097).
Definition r1_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17098).
Definition t64_2_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17099).
Definition t128_1_14 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17100).
Definition t128_2_3 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17101).
Definition r3_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17102).
Definition t64_3_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17103).
Definition r4_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17104).
Definition t64_4_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17105).
Definition r5_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17106).
Definition t64_5_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17107).
Definition r6_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17108).
Definition r2_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17109).

(* Signature *)
Definition tyin_A33____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 33; aword U64; aint; aint ].
Definition args_A33____addstate_avx2 : seq var_i :=
  [:: st_46.(gv)
    ; AT_43.(gv)
    ; buf_64.(gv)
    ; offset_57.(gv)
    ; _LEN_39.(gv)
    ; _TRAILB_23.(gv) ].
Definition tyout_A33____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A33____addstate_avx2 : seq var_i :=
  [:: st_46.(gv); AT_43.(gv); offset_57.(gv) ].

(* Body *)
Definition body_A33____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_39.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_43) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_39.(gv)
                                                                ; Lvar _LEN_39.(gv)
                                                                ; Lvar _TRAILB_23.(gv)
                                                                ; Lvar AT_43.(gv)
                                                                ; Lvar r0_8.(gv) ] A33____a_ilen_read_bcast_upto8_at [:: Pvar buf_64
                                                                    ; Pvar offset_57
                                                                    ; Pvar DELTA_39
                                                                    ; Pvar _LEN_39
                                                                    ; Pvar _TRAILB_23
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_43 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_46.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_46 (Pconst (0)%Z)) (Pvar r0_8))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_43) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_39)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_23) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_39.(gv)
                                                                ; Lvar _LEN_39.(gv)
                                                                ; Lvar _TRAILB_23.(gv)
                                                                ; Lvar AT_43.(gv)
                                                                ; Lvar r1_8.(gv) ] A33____a_ilen_read_upto32_at [:: Pvar buf_64
                                                                    ; Pvar offset_57
                                                                    ; Pvar DELTA_39
                                                                    ; Pvar _LEN_39
                                                                    ; Pvar _TRAILB_23
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_43 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_46.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_46 (Pconst (1)%Z)) (Pvar r1_8))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_39)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_23) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_39.(gv)
                                                                ; Lvar _LEN_39.(gv)
                                                                ; Lvar _TRAILB_23.(gv)
                                                                ; Lvar AT_43.(gv)
                                                                ; Lvar t64_2_3.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_64
                                                                    ; Pvar offset_57
                                                                    ; Pvar DELTA_39
                                                                    ; Pvar _LEN_39
                                                                    ; Pvar _TRAILB_23
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_43 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_14.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_3)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_3.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_39)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_23) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_39.(gv)
                                                                  ; Lvar _LEN_39.(gv)
                                                                  ; Lvar _TRAILB_23.(gv)
                                                                  ; Lvar AT_43.(gv)
                                                                  ; Lvar r3_8.(gv) ] A33____a_ilen_read_upto32_at [:: Pvar buf_64
                                                                    ; Pvar offset_57
                                                                    ; Pvar DELTA_39
                                                                    ; Pvar _LEN_39
                                                                    ; Pvar _TRAILB_23
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_43 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_39.(gv)
                                                                  ; Lvar _LEN_39.(gv)
                                                                  ; Lvar _TRAILB_23.(gv)
                                                                  ; Lvar AT_43.(gv)
                                                                  ; Lvar t64_3_3.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_64
                                                                    ; Pvar offset_57
                                                                    ; Pvar DELTA_39
                                                                    ; Pvar _LEN_39
                                                                    ; Pvar _TRAILB_23
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_43 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_3.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_3)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_39.(gv)
                                                                  ; Lvar _LEN_39.(gv)
                                                                  ; Lvar _TRAILB_23.(gv)
                                                                  ; Lvar AT_43.(gv)
                                                                  ; Lvar r4_8.(gv) ] A33____a_ilen_read_upto32_at [:: Pvar buf_64
                                                                    ; Pvar offset_57
                                                                    ; Pvar DELTA_39
                                                                    ; Pvar _LEN_39
                                                                    ; Pvar _TRAILB_23
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_43 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_39.(gv)
                                                                  ; Lvar _LEN_39.(gv)
                                                                  ; Lvar _TRAILB_23.(gv)
                                                                  ; Lvar AT_43.(gv)
                                                                  ; Lvar t64_4_3.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_64
                                                                    ; Pvar offset_57
                                                                    ; Pvar DELTA_39
                                                                    ; Pvar _LEN_39
                                                                    ; Pvar _TRAILB_23
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_43 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_14
                                                                    ; Pvar t64_4_3
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_39.(gv)
                                                                  ; Lvar _LEN_39.(gv)
                                                                  ; Lvar _TRAILB_23.(gv)
                                                                  ; Lvar AT_43.(gv)
                                                                  ; Lvar r5_8.(gv) ] A33____a_ilen_read_upto32_at [:: Pvar buf_64
                                                                    ; Pvar offset_57
                                                                    ; Pvar DELTA_39
                                                                    ; Pvar _LEN_39
                                                                    ; Pvar _TRAILB_23
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_43 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_39.(gv)
                                                                  ; Lvar _LEN_39.(gv)
                                                                  ; Lvar _TRAILB_23.(gv)
                                                                  ; Lvar AT_43.(gv)
                                                                  ; Lvar t64_5_3.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_64
                                                                    ; Pvar offset_57
                                                                    ; Pvar DELTA_39
                                                                    ; Pvar _LEN_39
                                                                    ; Pvar _TRAILB_23
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_43 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_3
                                                                    ; Pvar t64_5_3
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_39.(gv)
                                                                  ; Lvar _LEN_39.(gv)
                                                                  ; Lvar _TRAILB_23.(gv)
                                                                  ; Lvar AT_43.(gv)
                                                                  ; Lvar r6_8.(gv) ] A33____a_ilen_read_upto32_at [:: Pvar buf_64
                                                                    ; Pvar offset_57
                                                                    ; Pvar DELTA_39
                                                                    ; Pvar _LEN_39
                                                                    ; Pvar _TRAILB_23
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_43 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_46.(gv) ] __addstate_r3456_avx2 [:: Pvar st_46
                                                                    ; Pvar r3_8
                                                                    ; Pvar r4_8
                                                                    ; Pvar r5_8
                                                                    ; Pvar r6_8 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_5.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_3)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_5.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_5
                                                                    ; Pvar t128_1_14
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_46.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_46 (Pconst (2)%Z)) (Pvar r2_5))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_57.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_57) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_39)))) ].

Definition fd_A33____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____addstate_avx2;
    f_params := args_A33____addstate_avx2;
    f_body := body_A33____addstate_avx2;
    f_tyout := tyout_A33____addstate_avx2;
    f_res := res_A33____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
