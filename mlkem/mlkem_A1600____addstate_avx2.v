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

(* A1600____addstate_avx2 *)
(* Local variables *)
Definition st_100 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14933).
Definition AT_99 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14934).
Definition buf_146 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14935).
Definition offset_153 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14936).
Definition _LEN_93 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14937).
Definition _TRAILB_55 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14938).
Definition DELTA_103 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14939).
Definition r0_14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14940).
Definition r1_14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14941).
Definition t64_2_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14942).
Definition t128_1_32 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14943).
Definition t128_2_9 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14944).
Definition r3_14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14945).
Definition t64_3_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14946).
Definition r4_14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14947).
Definition t64_4_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14948).
Definition r5_14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14949).
Definition t64_5_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14950).
Definition r6_14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14951).
Definition r2_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14952).

(* Signature *)
Definition tyin_A1600____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1600; aword U64; aint; aint ].
Definition args_A1600____addstate_avx2 : seq var_i :=
  [:: st_100.(gv)
    ; AT_99.(gv)
    ; buf_146.(gv)
    ; offset_153.(gv)
    ; _LEN_93.(gv)
    ; _TRAILB_55.(gv) ].
Definition tyout_A1600____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A1600____addstate_avx2 : seq var_i :=
  [:: st_100.(gv); AT_99.(gv); offset_153.(gv) ].

(* Body *)
Definition body_A1600____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_103.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_99) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_103.(gv)
                                                                ; Lvar _LEN_93.(gv)
                                                                ; Lvar _TRAILB_55.(gv)
                                                                ; Lvar AT_99.(gv)
                                                                ; Lvar r0_14.(gv) ] A1600____a_ilen_read_bcast_upto8_at [:: Pvar buf_146
                                                                    ; Pvar offset_153
                                                                    ; Pvar DELTA_103
                                                                    ; Pvar _LEN_93
                                                                    ; Pvar _TRAILB_55
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_99 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_100.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_100 (Pconst (0)%Z)) (Pvar r0_14))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_99) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_93)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_55) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_103.(gv)
                                                                ; Lvar _LEN_93.(gv)
                                                                ; Lvar _TRAILB_55.(gv)
                                                                ; Lvar AT_99.(gv)
                                                                ; Lvar r1_14.(gv) ] A1600____a_ilen_read_upto32_at [:: Pvar buf_146
                                                                    ; Pvar offset_153
                                                                    ; Pvar DELTA_103
                                                                    ; Pvar _LEN_93
                                                                    ; Pvar _TRAILB_55
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_99 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_100.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_100 (Pconst (1)%Z)) (Pvar r1_14))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_93)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_55) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_103.(gv)
                                                                ; Lvar _LEN_93.(gv)
                                                                ; Lvar _TRAILB_55.(gv)
                                                                ; Lvar AT_99.(gv)
                                                                ; Lvar t64_2_9.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_146
                                                                    ; Pvar offset_153
                                                                    ; Pvar DELTA_103
                                                                    ; Pvar _LEN_93
                                                                    ; Pvar _TRAILB_55
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_99 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_32.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_9)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_9.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_93)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_55) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_103.(gv)
                                                                  ; Lvar _LEN_93.(gv)
                                                                  ; Lvar _TRAILB_55.(gv)
                                                                  ; Lvar AT_99.(gv)
                                                                  ; Lvar r3_14.(gv) ] A1600____a_ilen_read_upto32_at [:: Pvar buf_146
                                                                    ; Pvar offset_153
                                                                    ; Pvar DELTA_103
                                                                    ; Pvar _LEN_93
                                                                    ; Pvar _TRAILB_55
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_99 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_103.(gv)
                                                                  ; Lvar _LEN_93.(gv)
                                                                  ; Lvar _TRAILB_55.(gv)
                                                                  ; Lvar AT_99.(gv)
                                                                  ; Lvar t64_3_9.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_146
                                                                    ; Pvar offset_153
                                                                    ; Pvar DELTA_103
                                                                    ; Pvar _LEN_93
                                                                    ; Pvar _TRAILB_55
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_99 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_9.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_9)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_103.(gv)
                                                                  ; Lvar _LEN_93.(gv)
                                                                  ; Lvar _TRAILB_55.(gv)
                                                                  ; Lvar AT_99.(gv)
                                                                  ; Lvar r4_14.(gv) ] A1600____a_ilen_read_upto32_at [:: Pvar buf_146
                                                                    ; Pvar offset_153
                                                                    ; Pvar DELTA_103
                                                                    ; Pvar _LEN_93
                                                                    ; Pvar _TRAILB_55
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_99 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_103.(gv)
                                                                  ; Lvar _LEN_93.(gv)
                                                                  ; Lvar _TRAILB_55.(gv)
                                                                  ; Lvar AT_99.(gv)
                                                                  ; Lvar t64_4_9.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_146
                                                                    ; Pvar offset_153
                                                                    ; Pvar DELTA_103
                                                                    ; Pvar _LEN_93
                                                                    ; Pvar _TRAILB_55
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_99 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_32.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_32
                                                                    ; Pvar t64_4_9
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_103.(gv)
                                                                  ; Lvar _LEN_93.(gv)
                                                                  ; Lvar _TRAILB_55.(gv)
                                                                  ; Lvar AT_99.(gv)
                                                                  ; Lvar r5_14.(gv) ] A1600____a_ilen_read_upto32_at [:: Pvar buf_146
                                                                    ; Pvar offset_153
                                                                    ; Pvar DELTA_103
                                                                    ; Pvar _LEN_93
                                                                    ; Pvar _TRAILB_55
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_99 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_103.(gv)
                                                                  ; Lvar _LEN_93.(gv)
                                                                  ; Lvar _TRAILB_55.(gv)
                                                                  ; Lvar AT_99.(gv)
                                                                  ; Lvar t64_5_9.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_146
                                                                    ; Pvar offset_153
                                                                    ; Pvar DELTA_103
                                                                    ; Pvar _LEN_93
                                                                    ; Pvar _TRAILB_55
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_99 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_9
                                                                    ; Pvar t64_5_9
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_103.(gv)
                                                                  ; Lvar _LEN_93.(gv)
                                                                  ; Lvar _TRAILB_55.(gv)
                                                                  ; Lvar AT_99.(gv)
                                                                  ; Lvar r6_14.(gv) ] A1600____a_ilen_read_upto32_at [:: Pvar buf_146
                                                                    ; Pvar offset_153
                                                                    ; Pvar DELTA_103
                                                                    ; Pvar _LEN_93
                                                                    ; Pvar _TRAILB_55
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_99 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_100.(gv) ] __addstate_r3456_avx2 [:: Pvar st_100
                                                                    ; Pvar r3_14
                                                                    ; Pvar r4_14
                                                                    ; Pvar r5_14
                                                                    ; Pvar r6_14 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_11.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_9)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_11.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_11
                                                                    ; Pvar t128_1_32
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_100.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_100 (Pconst (2)%Z)) (Pvar r2_11))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_153.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_153) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_103)))) ].

Definition fd_A1600____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____addstate_avx2;
    f_params := args_A1600____addstate_avx2;
    f_body := body_A1600____addstate_avx2;
    f_tyout := tyout_A1600____addstate_avx2;
    f_res := res_A1600____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
