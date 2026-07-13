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

(* A1120____addstate_avx2 *)
(* Local variables *)
Definition st_90 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 15315).
Definition AT_89 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15316).
Definition buf_132 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15317).
Definition offset_136 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15318).
Definition _LEN_83 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15319).
Definition _TRAILB_49 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15320).
Definition DELTA_92 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15321).
Definition r0_13 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15322).
Definition r1_13 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15323).
Definition t64_2_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15324).
Definition t128_1_29 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15325).
Definition t128_2_8 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15326).
Definition r3_13 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15327).
Definition t64_3_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15328).
Definition r4_13 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15329).
Definition t64_4_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15330).
Definition r5_13 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15331).
Definition t64_5_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15332).
Definition r6_13 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15333).
Definition r2_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15334).

(* Signature *)
Definition tyin_A1120____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1120; aword U64; aint; aint ].
Definition args_A1120____addstate_avx2 : seq var_i :=
  [:: st_90.(gv)
    ; AT_89.(gv)
    ; buf_132.(gv)
    ; offset_136.(gv)
    ; _LEN_83.(gv)
    ; _TRAILB_49.(gv) ].
Definition tyout_A1120____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A1120____addstate_avx2 : seq var_i :=
  [:: st_90.(gv); AT_89.(gv); offset_136.(gv) ].

(* Body *)
Definition body_A1120____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_92.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_89) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_92.(gv)
                                                                ; Lvar _LEN_83.(gv)
                                                                ; Lvar _TRAILB_49.(gv)
                                                                ; Lvar AT_89.(gv)
                                                                ; Lvar r0_13.(gv) ] A1120____a_ilen_read_bcast_upto8_at [:: Pvar buf_132
                                                                    ; Pvar offset_136
                                                                    ; Pvar DELTA_92
                                                                    ; Pvar _LEN_83
                                                                    ; Pvar _TRAILB_49
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_89 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_90.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_90 (Pconst (0)%Z)) (Pvar r0_13))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_89) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_83)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_49) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_92.(gv)
                                                                ; Lvar _LEN_83.(gv)
                                                                ; Lvar _TRAILB_49.(gv)
                                                                ; Lvar AT_89.(gv)
                                                                ; Lvar r1_13.(gv) ] A1120____a_ilen_read_upto32_at [:: Pvar buf_132
                                                                    ; Pvar offset_136
                                                                    ; Pvar DELTA_92
                                                                    ; Pvar _LEN_83
                                                                    ; Pvar _TRAILB_49
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_89 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_90.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_90 (Pconst (1)%Z)) (Pvar r1_13))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_83)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_49) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_92.(gv)
                                                                ; Lvar _LEN_83.(gv)
                                                                ; Lvar _TRAILB_49.(gv)
                                                                ; Lvar AT_89.(gv)
                                                                ; Lvar t64_2_8.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_132
                                                                    ; Pvar offset_136
                                                                    ; Pvar DELTA_92
                                                                    ; Pvar _LEN_83
                                                                    ; Pvar _TRAILB_49
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_89 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_29.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_8)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_8.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_83)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_49) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_92.(gv)
                                                                  ; Lvar _LEN_83.(gv)
                                                                  ; Lvar _TRAILB_49.(gv)
                                                                  ; Lvar AT_89.(gv)
                                                                  ; Lvar r3_13.(gv) ] A1120____a_ilen_read_upto32_at [:: Pvar buf_132
                                                                    ; Pvar offset_136
                                                                    ; Pvar DELTA_92
                                                                    ; Pvar _LEN_83
                                                                    ; Pvar _TRAILB_49
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_89 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_92.(gv)
                                                                  ; Lvar _LEN_83.(gv)
                                                                  ; Lvar _TRAILB_49.(gv)
                                                                  ; Lvar AT_89.(gv)
                                                                  ; Lvar t64_3_8.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_132
                                                                    ; Pvar offset_136
                                                                    ; Pvar DELTA_92
                                                                    ; Pvar _LEN_83
                                                                    ; Pvar _TRAILB_49
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_89 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_8.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_8)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_92.(gv)
                                                                  ; Lvar _LEN_83.(gv)
                                                                  ; Lvar _TRAILB_49.(gv)
                                                                  ; Lvar AT_89.(gv)
                                                                  ; Lvar r4_13.(gv) ] A1120____a_ilen_read_upto32_at [:: Pvar buf_132
                                                                    ; Pvar offset_136
                                                                    ; Pvar DELTA_92
                                                                    ; Pvar _LEN_83
                                                                    ; Pvar _TRAILB_49
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_89 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_92.(gv)
                                                                  ; Lvar _LEN_83.(gv)
                                                                  ; Lvar _TRAILB_49.(gv)
                                                                  ; Lvar AT_89.(gv)
                                                                  ; Lvar t64_4_8.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_132
                                                                    ; Pvar offset_136
                                                                    ; Pvar DELTA_92
                                                                    ; Pvar _LEN_83
                                                                    ; Pvar _TRAILB_49
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_89 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_29.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_29
                                                                    ; Pvar t64_4_8
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_92.(gv)
                                                                  ; Lvar _LEN_83.(gv)
                                                                  ; Lvar _TRAILB_49.(gv)
                                                                  ; Lvar AT_89.(gv)
                                                                  ; Lvar r5_13.(gv) ] A1120____a_ilen_read_upto32_at [:: Pvar buf_132
                                                                    ; Pvar offset_136
                                                                    ; Pvar DELTA_92
                                                                    ; Pvar _LEN_83
                                                                    ; Pvar _TRAILB_49
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_89 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_92.(gv)
                                                                  ; Lvar _LEN_83.(gv)
                                                                  ; Lvar _TRAILB_49.(gv)
                                                                  ; Lvar AT_89.(gv)
                                                                  ; Lvar t64_5_8.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_132
                                                                    ; Pvar offset_136
                                                                    ; Pvar DELTA_92
                                                                    ; Pvar _LEN_83
                                                                    ; Pvar _TRAILB_49
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_89 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_8
                                                                    ; Pvar t64_5_8
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_92.(gv)
                                                                  ; Lvar _LEN_83.(gv)
                                                                  ; Lvar _TRAILB_49.(gv)
                                                                  ; Lvar AT_89.(gv)
                                                                  ; Lvar r6_13.(gv) ] A1120____a_ilen_read_upto32_at [:: Pvar buf_132
                                                                    ; Pvar offset_136
                                                                    ; Pvar DELTA_92
                                                                    ; Pvar _LEN_83
                                                                    ; Pvar _TRAILB_49
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_89 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_90.(gv) ] __addstate_r3456_avx2 [:: Pvar st_90
                                                                    ; Pvar r3_13
                                                                    ; Pvar r4_13
                                                                    ; Pvar r5_13
                                                                    ; Pvar r6_13 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_10.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_8)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_10.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_10
                                                                    ; Pvar t128_1_29
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_90.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_90 (Pconst (2)%Z)) (Pvar r2_10))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_136.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_136) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_92)))) ].

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
