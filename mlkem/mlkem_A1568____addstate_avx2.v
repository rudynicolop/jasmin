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

(* A1568____addstate_avx2 *)
(* Local variables *)
Definition st_80 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 15697).
Definition AT_79 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15698).
Definition buf_118 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15699).
Definition offset_119 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15700).
Definition _LEN_73 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15701).
Definition _TRAILB_43 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15702).
Definition DELTA_81 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15703).
Definition r0_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15704).
Definition r1_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15705).
Definition t64_2_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15706).
Definition t128_1_26 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15707).
Definition t128_2_7 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15708).
Definition r3_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15709).
Definition t64_3_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15710).
Definition r4_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15711).
Definition t64_4_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15712).
Definition r5_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15713).
Definition t64_5_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15714).
Definition r6_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15715).
Definition r2_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15716).

(* Signature *)
Definition tyin_A1568____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1568; aword U64; aint; aint ].
Definition args_A1568____addstate_avx2 : seq var_i :=
  [:: st_80.(gv)
    ; AT_79.(gv)
    ; buf_118.(gv)
    ; offset_119.(gv)
    ; _LEN_73.(gv)
    ; _TRAILB_43.(gv) ].
Definition tyout_A1568____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A1568____addstate_avx2 : seq var_i :=
  [:: st_80.(gv); AT_79.(gv); offset_119.(gv) ].

(* Body *)
Definition body_A1568____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_81.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_79) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_81.(gv)
                                                                ; Lvar _LEN_73.(gv)
                                                                ; Lvar _TRAILB_43.(gv)
                                                                ; Lvar AT_79.(gv)
                                                                ; Lvar r0_12.(gv) ] A1568____a_ilen_read_bcast_upto8_at [:: Pvar buf_118
                                                                    ; Pvar offset_119
                                                                    ; Pvar DELTA_81
                                                                    ; Pvar _LEN_73
                                                                    ; Pvar _TRAILB_43
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_79 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_80.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_80 (Pconst (0)%Z)) (Pvar r0_12))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_79) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_73)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_43) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_81.(gv)
                                                                ; Lvar _LEN_73.(gv)
                                                                ; Lvar _TRAILB_43.(gv)
                                                                ; Lvar AT_79.(gv)
                                                                ; Lvar r1_12.(gv) ] A1568____a_ilen_read_upto32_at [:: Pvar buf_118
                                                                    ; Pvar offset_119
                                                                    ; Pvar DELTA_81
                                                                    ; Pvar _LEN_73
                                                                    ; Pvar _TRAILB_43
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_79 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_80.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_80 (Pconst (1)%Z)) (Pvar r1_12))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_73)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_43) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_81.(gv)
                                                                ; Lvar _LEN_73.(gv)
                                                                ; Lvar _TRAILB_43.(gv)
                                                                ; Lvar AT_79.(gv)
                                                                ; Lvar t64_2_7.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_118
                                                                    ; Pvar offset_119
                                                                    ; Pvar DELTA_81
                                                                    ; Pvar _LEN_73
                                                                    ; Pvar _TRAILB_43
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_79 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_26.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_7)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_7.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_73)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_43) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_81.(gv)
                                                                  ; Lvar _LEN_73.(gv)
                                                                  ; Lvar _TRAILB_43.(gv)
                                                                  ; Lvar AT_79.(gv)
                                                                  ; Lvar r3_12.(gv) ] A1568____a_ilen_read_upto32_at [:: Pvar buf_118
                                                                    ; Pvar offset_119
                                                                    ; Pvar DELTA_81
                                                                    ; Pvar _LEN_73
                                                                    ; Pvar _TRAILB_43
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_79 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_81.(gv)
                                                                  ; Lvar _LEN_73.(gv)
                                                                  ; Lvar _TRAILB_43.(gv)
                                                                  ; Lvar AT_79.(gv)
                                                                  ; Lvar t64_3_7.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_118
                                                                    ; Pvar offset_119
                                                                    ; Pvar DELTA_81
                                                                    ; Pvar _LEN_73
                                                                    ; Pvar _TRAILB_43
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_79 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_7.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_7)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_81.(gv)
                                                                  ; Lvar _LEN_73.(gv)
                                                                  ; Lvar _TRAILB_43.(gv)
                                                                  ; Lvar AT_79.(gv)
                                                                  ; Lvar r4_12.(gv) ] A1568____a_ilen_read_upto32_at [:: Pvar buf_118
                                                                    ; Pvar offset_119
                                                                    ; Pvar DELTA_81
                                                                    ; Pvar _LEN_73
                                                                    ; Pvar _TRAILB_43
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_79 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_81.(gv)
                                                                  ; Lvar _LEN_73.(gv)
                                                                  ; Lvar _TRAILB_43.(gv)
                                                                  ; Lvar AT_79.(gv)
                                                                  ; Lvar t64_4_7.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_118
                                                                    ; Pvar offset_119
                                                                    ; Pvar DELTA_81
                                                                    ; Pvar _LEN_73
                                                                    ; Pvar _TRAILB_43
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_79 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_26.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_26
                                                                    ; Pvar t64_4_7
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_81.(gv)
                                                                  ; Lvar _LEN_73.(gv)
                                                                  ; Lvar _TRAILB_43.(gv)
                                                                  ; Lvar AT_79.(gv)
                                                                  ; Lvar r5_12.(gv) ] A1568____a_ilen_read_upto32_at [:: Pvar buf_118
                                                                    ; Pvar offset_119
                                                                    ; Pvar DELTA_81
                                                                    ; Pvar _LEN_73
                                                                    ; Pvar _TRAILB_43
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_79 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_81.(gv)
                                                                  ; Lvar _LEN_73.(gv)
                                                                  ; Lvar _TRAILB_43.(gv)
                                                                  ; Lvar AT_79.(gv)
                                                                  ; Lvar t64_5_7.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_118
                                                                    ; Pvar offset_119
                                                                    ; Pvar DELTA_81
                                                                    ; Pvar _LEN_73
                                                                    ; Pvar _TRAILB_43
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_79 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_7
                                                                    ; Pvar t64_5_7
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_81.(gv)
                                                                  ; Lvar _LEN_73.(gv)
                                                                  ; Lvar _TRAILB_43.(gv)
                                                                  ; Lvar AT_79.(gv)
                                                                  ; Lvar r6_12.(gv) ] A1568____a_ilen_read_upto32_at [:: Pvar buf_118
                                                                    ; Pvar offset_119
                                                                    ; Pvar DELTA_81
                                                                    ; Pvar _LEN_73
                                                                    ; Pvar _TRAILB_43
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_79 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_80.(gv) ] __addstate_r3456_avx2 [:: Pvar st_80
                                                                    ; Pvar r3_12
                                                                    ; Pvar r4_12
                                                                    ; Pvar r5_12
                                                                    ; Pvar r6_12 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_9.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_7)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_9.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_9
                                                                    ; Pvar t128_1_26
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_80.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_80 (Pconst (2)%Z)) (Pvar r2_9))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_119.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_119) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_81)))) ].

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
