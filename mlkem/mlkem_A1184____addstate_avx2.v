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

(* A1184____addstate_avx2 *)
(* Local variables *)
Definition st_70 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16079).
Definition AT_69 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16080).
Definition buf_104 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16081).
Definition offset_102 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16082).
Definition _LEN_63 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16083).
Definition _TRAILB_37 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16084).
Definition DELTA_70 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16085).
Definition r0_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16086).
Definition r1_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16087).
Definition t64_2_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16088).
Definition t128_1_23 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16089).
Definition t128_2_6 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16090).
Definition r3_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16091).
Definition t64_3_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16092).
Definition r4_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16093).
Definition t64_4_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16094).
Definition r5_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16095).
Definition t64_5_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16096).
Definition r6_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16097).
Definition r2_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16098).

(* Signature *)
Definition tyin_A1184____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1184; aword U64; aint; aint ].
Definition args_A1184____addstate_avx2 : seq var_i :=
  [:: st_70.(gv)
    ; AT_69.(gv)
    ; buf_104.(gv)
    ; offset_102.(gv)
    ; _LEN_63.(gv)
    ; _TRAILB_37.(gv) ].
Definition tyout_A1184____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A1184____addstate_avx2 : seq var_i :=
  [:: st_70.(gv); AT_69.(gv); offset_102.(gv) ].

(* Body *)
Definition body_A1184____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_70.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_69) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_70.(gv)
                                                                ; Lvar _LEN_63.(gv)
                                                                ; Lvar _TRAILB_37.(gv)
                                                                ; Lvar AT_69.(gv)
                                                                ; Lvar r0_11.(gv) ] A1184____a_ilen_read_bcast_upto8_at [:: Pvar buf_104
                                                                    ; Pvar offset_102
                                                                    ; Pvar DELTA_70
                                                                    ; Pvar _LEN_63
                                                                    ; Pvar _TRAILB_37
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_69 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_70.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_70 (Pconst (0)%Z)) (Pvar r0_11))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_69) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_63)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_37) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_70.(gv)
                                                                ; Lvar _LEN_63.(gv)
                                                                ; Lvar _TRAILB_37.(gv)
                                                                ; Lvar AT_69.(gv)
                                                                ; Lvar r1_11.(gv) ] A1184____a_ilen_read_upto32_at [:: Pvar buf_104
                                                                    ; Pvar offset_102
                                                                    ; Pvar DELTA_70
                                                                    ; Pvar _LEN_63
                                                                    ; Pvar _TRAILB_37
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_69 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_70.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_70 (Pconst (1)%Z)) (Pvar r1_11))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_63)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_37) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_70.(gv)
                                                                ; Lvar _LEN_63.(gv)
                                                                ; Lvar _TRAILB_37.(gv)
                                                                ; Lvar AT_69.(gv)
                                                                ; Lvar t64_2_6.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_104
                                                                    ; Pvar offset_102
                                                                    ; Pvar DELTA_70
                                                                    ; Pvar _LEN_63
                                                                    ; Pvar _TRAILB_37
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_69 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_23.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_6)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_6.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_63)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_37) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_70.(gv)
                                                                  ; Lvar _LEN_63.(gv)
                                                                  ; Lvar _TRAILB_37.(gv)
                                                                  ; Lvar AT_69.(gv)
                                                                  ; Lvar r3_11.(gv) ] A1184____a_ilen_read_upto32_at [:: Pvar buf_104
                                                                    ; Pvar offset_102
                                                                    ; Pvar DELTA_70
                                                                    ; Pvar _LEN_63
                                                                    ; Pvar _TRAILB_37
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_69 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_70.(gv)
                                                                  ; Lvar _LEN_63.(gv)
                                                                  ; Lvar _TRAILB_37.(gv)
                                                                  ; Lvar AT_69.(gv)
                                                                  ; Lvar t64_3_6.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_104
                                                                    ; Pvar offset_102
                                                                    ; Pvar DELTA_70
                                                                    ; Pvar _LEN_63
                                                                    ; Pvar _TRAILB_37
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_69 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_6.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_6)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_70.(gv)
                                                                  ; Lvar _LEN_63.(gv)
                                                                  ; Lvar _TRAILB_37.(gv)
                                                                  ; Lvar AT_69.(gv)
                                                                  ; Lvar r4_11.(gv) ] A1184____a_ilen_read_upto32_at [:: Pvar buf_104
                                                                    ; Pvar offset_102
                                                                    ; Pvar DELTA_70
                                                                    ; Pvar _LEN_63
                                                                    ; Pvar _TRAILB_37
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_69 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_70.(gv)
                                                                  ; Lvar _LEN_63.(gv)
                                                                  ; Lvar _TRAILB_37.(gv)
                                                                  ; Lvar AT_69.(gv)
                                                                  ; Lvar t64_4_6.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_104
                                                                    ; Pvar offset_102
                                                                    ; Pvar DELTA_70
                                                                    ; Pvar _LEN_63
                                                                    ; Pvar _TRAILB_37
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_69 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_23.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_23
                                                                    ; Pvar t64_4_6
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_70.(gv)
                                                                  ; Lvar _LEN_63.(gv)
                                                                  ; Lvar _TRAILB_37.(gv)
                                                                  ; Lvar AT_69.(gv)
                                                                  ; Lvar r5_11.(gv) ] A1184____a_ilen_read_upto32_at [:: Pvar buf_104
                                                                    ; Pvar offset_102
                                                                    ; Pvar DELTA_70
                                                                    ; Pvar _LEN_63
                                                                    ; Pvar _TRAILB_37
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_69 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_70.(gv)
                                                                  ; Lvar _LEN_63.(gv)
                                                                  ; Lvar _TRAILB_37.(gv)
                                                                  ; Lvar AT_69.(gv)
                                                                  ; Lvar t64_5_6.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_104
                                                                    ; Pvar offset_102
                                                                    ; Pvar DELTA_70
                                                                    ; Pvar _LEN_63
                                                                    ; Pvar _TRAILB_37
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_69 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_6
                                                                    ; Pvar t64_5_6
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_70.(gv)
                                                                  ; Lvar _LEN_63.(gv)
                                                                  ; Lvar _TRAILB_37.(gv)
                                                                  ; Lvar AT_69.(gv)
                                                                  ; Lvar r6_11.(gv) ] A1184____a_ilen_read_upto32_at [:: Pvar buf_104
                                                                    ; Pvar offset_102
                                                                    ; Pvar DELTA_70
                                                                    ; Pvar _LEN_63
                                                                    ; Pvar _TRAILB_37
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_69 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_70.(gv) ] __addstate_r3456_avx2 [:: Pvar st_70
                                                                    ; Pvar r3_11
                                                                    ; Pvar r4_11
                                                                    ; Pvar r5_11
                                                                    ; Pvar r6_11 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_8.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_6)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_8.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_8
                                                                    ; Pvar t128_1_23
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_70.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_70 (Pconst (2)%Z)) (Pvar r2_8))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_102.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_102) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_70)))) ].

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
