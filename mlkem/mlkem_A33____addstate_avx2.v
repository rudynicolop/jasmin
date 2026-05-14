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
Definition st_17090 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 17090).
Definition AT_17091 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17091).
Definition buf_17092 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17092).
Definition offset_17093 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17093).
Definition _LEN_17094 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17094).
Definition _TRAILB_17095 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17095).
Definition DELTA_17096 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17096).
Definition r0_17097 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17097).
Definition r1_17098 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17098).
Definition t64_2_17099 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17099).
Definition t128_1_17100 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17100).
Definition t128_2_17101 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17101).
Definition r3_17102 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17102).
Definition t64_3_17103 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17103).
Definition r4_17104 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17104).
Definition t64_4_17105 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17105).
Definition r5_17106 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17106).
Definition t64_5_17107 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17107).
Definition r6_17108 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17108).
Definition r2_17109 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17109).

(* Signature *)
Definition tyin_A33____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 33; aword U64; aint; aint ].
Definition args_A33____addstate_avx2 : seq var_i :=
  [:: st_17090.(gv)
    ; AT_17091.(gv)
    ; buf_17092.(gv)
    ; offset_17093.(gv)
    ; _LEN_17094.(gv)
    ; _TRAILB_17095.(gv) ].
Definition tyout_A33____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A33____addstate_avx2 : seq var_i :=
  [:: st_17090.(gv); AT_17091.(gv); offset_17093.(gv) ].

(* Body *)
Definition body_A33____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_17096.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_17091) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17096.(gv)
                                                                ; Lvar _LEN_17094.(gv)
                                                                ; Lvar _TRAILB_17095.(gv)
                                                                ; Lvar AT_17091.(gv)
                                                                ; Lvar r0_17097.(gv) ] A33____a_ilen_read_bcast_upto8_at [:: Pvar buf_17092
                                                                    ; Pvar offset_17093
                                                                    ; Pvar DELTA_17096
                                                                    ; Pvar _LEN_17094
                                                                    ; Pvar _TRAILB_17095
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_17091 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_17090.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_17090 (Pconst (0)%Z)) (Pvar r0_17097))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_17091) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17094)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17095) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17096.(gv)
                                                                ; Lvar _LEN_17094.(gv)
                                                                ; Lvar _TRAILB_17095.(gv)
                                                                ; Lvar AT_17091.(gv)
                                                                ; Lvar r1_17098.(gv) ] A33____a_ilen_read_upto32_at [:: Pvar buf_17092
                                                                    ; Pvar offset_17093
                                                                    ; Pvar DELTA_17096
                                                                    ; Pvar _LEN_17094
                                                                    ; Pvar _TRAILB_17095
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_17091 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_17090.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_17090 (Pconst (1)%Z)) (Pvar r1_17098))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17094)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17095) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17096.(gv)
                                                                ; Lvar _LEN_17094.(gv)
                                                                ; Lvar _TRAILB_17095.(gv)
                                                                ; Lvar AT_17091.(gv)
                                                                ; Lvar t64_2_17099.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_17092
                                                                    ; Pvar offset_17093
                                                                    ; Pvar DELTA_17096
                                                                    ; Pvar _LEN_17094
                                                                    ; Pvar _TRAILB_17095
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_17091 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_17100.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_17099)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_17101.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17094)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17095) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17096.(gv)
                                                                  ; Lvar _LEN_17094.(gv)
                                                                  ; Lvar _TRAILB_17095.(gv)
                                                                  ; Lvar AT_17091.(gv)
                                                                  ; Lvar r3_17102.(gv) ] A33____a_ilen_read_upto32_at [:: Pvar buf_17092
                                                                    ; Pvar offset_17093
                                                                    ; Pvar DELTA_17096
                                                                    ; Pvar _LEN_17094
                                                                    ; Pvar _TRAILB_17095
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_17091 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17096.(gv)
                                                                  ; Lvar _LEN_17094.(gv)
                                                                  ; Lvar _TRAILB_17095.(gv)
                                                                  ; Lvar AT_17091.(gv)
                                                                  ; Lvar t64_3_17103.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_17092
                                                                    ; Pvar offset_17093
                                                                    ; Pvar DELTA_17096
                                                                    ; Pvar _LEN_17094
                                                                    ; Pvar _TRAILB_17095
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_17091 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_17101.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_17103)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17096.(gv)
                                                                  ; Lvar _LEN_17094.(gv)
                                                                  ; Lvar _TRAILB_17095.(gv)
                                                                  ; Lvar AT_17091.(gv)
                                                                  ; Lvar r4_17104.(gv) ] A33____a_ilen_read_upto32_at [:: Pvar buf_17092
                                                                    ; Pvar offset_17093
                                                                    ; Pvar DELTA_17096
                                                                    ; Pvar _LEN_17094
                                                                    ; Pvar _TRAILB_17095
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_17091 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17096.(gv)
                                                                  ; Lvar _LEN_17094.(gv)
                                                                  ; Lvar _TRAILB_17095.(gv)
                                                                  ; Lvar AT_17091.(gv)
                                                                  ; Lvar t64_4_17105.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_17092
                                                                    ; Pvar offset_17093
                                                                    ; Pvar DELTA_17096
                                                                    ; Pvar _LEN_17094
                                                                    ; Pvar _TRAILB_17095
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_17091 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_17100.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_17100
                                                                    ; Pvar t64_4_17105
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17096.(gv)
                                                                  ; Lvar _LEN_17094.(gv)
                                                                  ; Lvar _TRAILB_17095.(gv)
                                                                  ; Lvar AT_17091.(gv)
                                                                  ; Lvar r5_17106.(gv) ] A33____a_ilen_read_upto32_at [:: Pvar buf_17092
                                                                    ; Pvar offset_17093
                                                                    ; Pvar DELTA_17096
                                                                    ; Pvar _LEN_17094
                                                                    ; Pvar _TRAILB_17095
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_17091 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17096.(gv)
                                                                  ; Lvar _LEN_17094.(gv)
                                                                  ; Lvar _TRAILB_17095.(gv)
                                                                  ; Lvar AT_17091.(gv)
                                                                  ; Lvar t64_5_17107.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_17092
                                                                    ; Pvar offset_17093
                                                                    ; Pvar DELTA_17096
                                                                    ; Pvar _LEN_17094
                                                                    ; Pvar _TRAILB_17095
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_17091 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_17101.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_17101
                                                                    ; Pvar t64_5_17107
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17096.(gv)
                                                                  ; Lvar _LEN_17094.(gv)
                                                                  ; Lvar _TRAILB_17095.(gv)
                                                                  ; Lvar AT_17091.(gv)
                                                                  ; Lvar r6_17108.(gv) ] A33____a_ilen_read_upto32_at [:: Pvar buf_17092
                                                                    ; Pvar offset_17093
                                                                    ; Pvar DELTA_17096
                                                                    ; Pvar _LEN_17094
                                                                    ; Pvar _TRAILB_17095
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_17091 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_17090.(gv) ] __addstate_r3456_avx2 [:: Pvar st_17090
                                                                    ; Pvar r3_17102
                                                                    ; Pvar r4_17104
                                                                    ; Pvar r5_17106
                                                                    ; Pvar r6_17108 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_17109.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_17101)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_17109.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_17109
                                                                    ; Pvar t128_1_17100
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_17090.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_17090 (Pconst (2)%Z)) (Pvar r2_17109))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_17093.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17093) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17096)))) ].

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
