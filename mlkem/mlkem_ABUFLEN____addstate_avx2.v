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

(* ABUFLEN____addstate_avx2 *)
(* Local variables *)
Definition st_110 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14551).
Definition AT_109 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14552).
Definition buf_160 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14553).
Definition offset_170 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14554).
Definition _LEN_103 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14555).
Definition _TRAILB_61 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14556).
Definition DELTA_114 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14557).
Definition r0_15 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14558).
Definition r1_15 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14559).
Definition t64_2_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14560).
Definition t128_1_35 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14561).
Definition t128_2_10 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14562).
Definition r3_15 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14563).
Definition t64_3_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14564).
Definition r4_15 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14565).
Definition t64_4_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14566).
Definition r5_15 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14567).
Definition t64_5_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14568).
Definition r6_15 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14569).
Definition r2_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14570).

(* Signature *)
Definition tyin_ABUFLEN____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 536; aword U64; aint; aint ].
Definition args_ABUFLEN____addstate_avx2 : seq var_i :=
  [:: st_110.(gv)
    ; AT_109.(gv)
    ; buf_160.(gv)
    ; offset_170.(gv)
    ; _LEN_103.(gv)
    ; _TRAILB_61.(gv) ].
Definition tyout_ABUFLEN____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_ABUFLEN____addstate_avx2 : seq var_i :=
  [:: st_110.(gv); AT_109.(gv); offset_170.(gv) ].

(* Body *)
Definition body_ABUFLEN____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_114.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_109) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_114.(gv)
                                                                ; Lvar _LEN_103.(gv)
                                                                ; Lvar _TRAILB_61.(gv)
                                                                ; Lvar AT_109.(gv)
                                                                ; Lvar r0_15.(gv) ] ABUFLEN____a_ilen_read_bcast_upto8_at [:: Pvar buf_160
                                                                    ; Pvar offset_170
                                                                    ; Pvar DELTA_114
                                                                    ; Pvar _LEN_103
                                                                    ; Pvar _TRAILB_61
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_109 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_110.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_110 (Pconst (0)%Z)) (Pvar r0_15))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_109) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_103)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_61) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_114.(gv)
                                                                ; Lvar _LEN_103.(gv)
                                                                ; Lvar _TRAILB_61.(gv)
                                                                ; Lvar AT_109.(gv)
                                                                ; Lvar r1_15.(gv) ] ABUFLEN____a_ilen_read_upto32_at [:: Pvar buf_160
                                                                    ; Pvar offset_170
                                                                    ; Pvar DELTA_114
                                                                    ; Pvar _LEN_103
                                                                    ; Pvar _TRAILB_61
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_109 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_110.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_110 (Pconst (1)%Z)) (Pvar r1_15))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_103)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_61) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_114.(gv)
                                                                ; Lvar _LEN_103.(gv)
                                                                ; Lvar _TRAILB_61.(gv)
                                                                ; Lvar AT_109.(gv)
                                                                ; Lvar t64_2_10.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_160
                                                                    ; Pvar offset_170
                                                                    ; Pvar DELTA_114
                                                                    ; Pvar _LEN_103
                                                                    ; Pvar _TRAILB_61
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_109 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_35.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_10)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_10.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_103)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_61) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_114.(gv)
                                                                  ; Lvar _LEN_103.(gv)
                                                                  ; Lvar _TRAILB_61.(gv)
                                                                  ; Lvar AT_109.(gv)
                                                                  ; Lvar r3_15.(gv) ] ABUFLEN____a_ilen_read_upto32_at [:: Pvar buf_160
                                                                    ; Pvar offset_170
                                                                    ; Pvar DELTA_114
                                                                    ; Pvar _LEN_103
                                                                    ; Pvar _TRAILB_61
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_109 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_114.(gv)
                                                                  ; Lvar _LEN_103.(gv)
                                                                  ; Lvar _TRAILB_61.(gv)
                                                                  ; Lvar AT_109.(gv)
                                                                  ; Lvar t64_3_10.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_160
                                                                    ; Pvar offset_170
                                                                    ; Pvar DELTA_114
                                                                    ; Pvar _LEN_103
                                                                    ; Pvar _TRAILB_61
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_109 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_10.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_10)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_114.(gv)
                                                                  ; Lvar _LEN_103.(gv)
                                                                  ; Lvar _TRAILB_61.(gv)
                                                                  ; Lvar AT_109.(gv)
                                                                  ; Lvar r4_15.(gv) ] ABUFLEN____a_ilen_read_upto32_at [:: Pvar buf_160
                                                                    ; Pvar offset_170
                                                                    ; Pvar DELTA_114
                                                                    ; Pvar _LEN_103
                                                                    ; Pvar _TRAILB_61
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_109 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_114.(gv)
                                                                  ; Lvar _LEN_103.(gv)
                                                                  ; Lvar _TRAILB_61.(gv)
                                                                  ; Lvar AT_109.(gv)
                                                                  ; Lvar t64_4_10.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_160
                                                                    ; Pvar offset_170
                                                                    ; Pvar DELTA_114
                                                                    ; Pvar _LEN_103
                                                                    ; Pvar _TRAILB_61
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_109 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_35.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_35
                                                                    ; Pvar t64_4_10
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_114.(gv)
                                                                  ; Lvar _LEN_103.(gv)
                                                                  ; Lvar _TRAILB_61.(gv)
                                                                  ; Lvar AT_109.(gv)
                                                                  ; Lvar r5_15.(gv) ] ABUFLEN____a_ilen_read_upto32_at [:: Pvar buf_160
                                                                    ; Pvar offset_170
                                                                    ; Pvar DELTA_114
                                                                    ; Pvar _LEN_103
                                                                    ; Pvar _TRAILB_61
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_109 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_114.(gv)
                                                                  ; Lvar _LEN_103.(gv)
                                                                  ; Lvar _TRAILB_61.(gv)
                                                                  ; Lvar AT_109.(gv)
                                                                  ; Lvar t64_5_10.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_160
                                                                    ; Pvar offset_170
                                                                    ; Pvar DELTA_114
                                                                    ; Pvar _LEN_103
                                                                    ; Pvar _TRAILB_61
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_109 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_10
                                                                    ; Pvar t64_5_10
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_114.(gv)
                                                                  ; Lvar _LEN_103.(gv)
                                                                  ; Lvar _TRAILB_61.(gv)
                                                                  ; Lvar AT_109.(gv)
                                                                  ; Lvar r6_15.(gv) ] ABUFLEN____a_ilen_read_upto32_at [:: Pvar buf_160
                                                                    ; Pvar offset_170
                                                                    ; Pvar DELTA_114
                                                                    ; Pvar _LEN_103
                                                                    ; Pvar _TRAILB_61
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_109 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_110.(gv) ] __addstate_r3456_avx2 [:: Pvar st_110
                                                                    ; Pvar r3_15
                                                                    ; Pvar r4_15
                                                                    ; Pvar r5_15
                                                                    ; Pvar r6_15 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_12.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_10)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_12.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_12
                                                                    ; Pvar t128_1_35
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_110.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_110 (Pconst (2)%Z)) (Pvar r2_12))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_170.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_170) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_114)))) ].

Definition fd_ABUFLEN____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____addstate_avx2;
    f_params := args_ABUFLEN____addstate_avx2;
    f_body := body_ABUFLEN____addstate_avx2;
    f_tyout := tyout_ABUFLEN____addstate_avx2;
    f_res := res_ABUFLEN____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
