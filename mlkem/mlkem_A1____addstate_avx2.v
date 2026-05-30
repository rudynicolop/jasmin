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

(* A1____addstate_avx2 *)
(* Local variables *)
Definition st_16 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 18236).
Definition AT_13 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18237).
Definition buf_22 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18238).
Definition offset_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18239).
Definition _LEN_9 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18240).
Definition _TRAILB_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18241).
Definition DELTA_6 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18242).
Definition r0_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18243).
Definition r1_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18244).
Definition t64_2_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18245).
Definition t128_1_5 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18246).
Definition t128_2_0 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18247).
Definition r3_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18248).
Definition t64_3_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18249).
Definition r4_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18250).
Definition t64_4_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18251).
Definition r5_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18252).
Definition t64_5_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18253).
Definition r6_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18254).
Definition r2_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18255).

(* Signature *)
Definition tyin_A1____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1; aword U64; aint; aint ].
Definition args_A1____addstate_avx2 : seq var_i :=
  [:: st_16.(gv)
    ; AT_13.(gv)
    ; buf_22.(gv)
    ; offset_6.(gv)
    ; _LEN_9.(gv)
    ; _TRAILB_5.(gv) ].
Definition tyout_A1____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A1____addstate_avx2 : seq var_i :=
  [:: st_16.(gv); AT_13.(gv); offset_6.(gv) ].

(* Body *)
Definition body_A1____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_6.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_13) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_6.(gv)
                                                                ; Lvar _LEN_9.(gv)
                                                                ; Lvar _TRAILB_5.(gv)
                                                                ; Lvar AT_13.(gv)
                                                                ; Lvar r0_5.(gv) ] A1____a_ilen_read_bcast_upto8_at [:: Pvar buf_22
                                                                    ; Pvar offset_6
                                                                    ; Pvar DELTA_6
                                                                    ; Pvar _LEN_9
                                                                    ; Pvar _TRAILB_5
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_13 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_16.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16 (Pconst (0)%Z)) (Pvar r0_5))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_13) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_9)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_5) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_6.(gv)
                                                                ; Lvar _LEN_9.(gv)
                                                                ; Lvar _TRAILB_5.(gv)
                                                                ; Lvar AT_13.(gv)
                                                                ; Lvar r1_5.(gv) ] A1____a_ilen_read_upto32_at [:: Pvar buf_22
                                                                    ; Pvar offset_6
                                                                    ; Pvar DELTA_6
                                                                    ; Pvar _LEN_9
                                                                    ; Pvar _TRAILB_5
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_13 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_16.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16 (Pconst (1)%Z)) (Pvar r1_5))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_9)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_5) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_6.(gv)
                                                                ; Lvar _LEN_9.(gv)
                                                                ; Lvar _TRAILB_5.(gv)
                                                                ; Lvar AT_13.(gv)
                                                                ; Lvar t64_2_0.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_22
                                                                    ; Pvar offset_6
                                                                    ; Pvar DELTA_6
                                                                    ; Pvar _LEN_9
                                                                    ; Pvar _TRAILB_5
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_13 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_5.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_0)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_0.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_9)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_5) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_6.(gv)
                                                                  ; Lvar _LEN_9.(gv)
                                                                  ; Lvar _TRAILB_5.(gv)
                                                                  ; Lvar AT_13.(gv)
                                                                  ; Lvar r3_5.(gv) ] A1____a_ilen_read_upto32_at [:: Pvar buf_22
                                                                    ; Pvar offset_6
                                                                    ; Pvar DELTA_6
                                                                    ; Pvar _LEN_9
                                                                    ; Pvar _TRAILB_5
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_13 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_6.(gv)
                                                                  ; Lvar _LEN_9.(gv)
                                                                  ; Lvar _TRAILB_5.(gv)
                                                                  ; Lvar AT_13.(gv)
                                                                  ; Lvar t64_3_0.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_22
                                                                    ; Pvar offset_6
                                                                    ; Pvar DELTA_6
                                                                    ; Pvar _LEN_9
                                                                    ; Pvar _TRAILB_5
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_13 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_0.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_0)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_6.(gv)
                                                                  ; Lvar _LEN_9.(gv)
                                                                  ; Lvar _TRAILB_5.(gv)
                                                                  ; Lvar AT_13.(gv)
                                                                  ; Lvar r4_5.(gv) ] A1____a_ilen_read_upto32_at [:: Pvar buf_22
                                                                    ; Pvar offset_6
                                                                    ; Pvar DELTA_6
                                                                    ; Pvar _LEN_9
                                                                    ; Pvar _TRAILB_5
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_13 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_6.(gv)
                                                                  ; Lvar _LEN_9.(gv)
                                                                  ; Lvar _TRAILB_5.(gv)
                                                                  ; Lvar AT_13.(gv)
                                                                  ; Lvar t64_4_0.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_22
                                                                    ; Pvar offset_6
                                                                    ; Pvar DELTA_6
                                                                    ; Pvar _LEN_9
                                                                    ; Pvar _TRAILB_5
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_13 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_5
                                                                    ; Pvar t64_4_0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_6.(gv)
                                                                  ; Lvar _LEN_9.(gv)
                                                                  ; Lvar _TRAILB_5.(gv)
                                                                  ; Lvar AT_13.(gv)
                                                                  ; Lvar r5_5.(gv) ] A1____a_ilen_read_upto32_at [:: Pvar buf_22
                                                                    ; Pvar offset_6
                                                                    ; Pvar DELTA_6
                                                                    ; Pvar _LEN_9
                                                                    ; Pvar _TRAILB_5
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_13 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_6.(gv)
                                                                  ; Lvar _LEN_9.(gv)
                                                                  ; Lvar _TRAILB_5.(gv)
                                                                  ; Lvar AT_13.(gv)
                                                                  ; Lvar t64_5_0.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_22
                                                                    ; Pvar offset_6
                                                                    ; Pvar DELTA_6
                                                                    ; Pvar _LEN_9
                                                                    ; Pvar _TRAILB_5
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_13 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_0
                                                                    ; Pvar t64_5_0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_6.(gv)
                                                                  ; Lvar _LEN_9.(gv)
                                                                  ; Lvar _TRAILB_5.(gv)
                                                                  ; Lvar AT_13.(gv)
                                                                  ; Lvar r6_5.(gv) ] A1____a_ilen_read_upto32_at [:: Pvar buf_22
                                                                    ; Pvar offset_6
                                                                    ; Pvar DELTA_6
                                                                    ; Pvar _LEN_9
                                                                    ; Pvar _TRAILB_5
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_13 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_16.(gv) ] __addstate_r3456_avx2 [:: Pvar st_16
                                                                    ; Pvar r3_5
                                                                    ; Pvar r4_5
                                                                    ; Pvar r5_5
                                                                    ; Pvar r6_5 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_2.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_0)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_2.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_2
                                                                    ; Pvar t128_1_5
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_16.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_16 (Pconst (2)%Z)) (Pvar r2_2))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_6.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_6)))) ].

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
