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

(* A128____addstate_avx2 *)
(* Local variables *)
Definition st_60 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16461).
Definition AT_59 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16462).
Definition buf_90 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16463).
Definition offset_85 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16464).
Definition _LEN_53 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16465).
Definition _TRAILB_31 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16466).
Definition DELTA_59 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16467).
Definition r0_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16468).
Definition r1_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16469).
Definition t64_2_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16470).
Definition t128_1_20 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16471).
Definition t128_2_5 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16472).
Definition r3_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16473).
Definition t64_3_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16474).
Definition r4_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16475).
Definition t64_4_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16476).
Definition r5_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16477).
Definition t64_5_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16478).
Definition r6_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16479).
Definition r2_7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16480).

(* Signature *)
Definition tyin_A128____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 128; aword U64; aint; aint ].
Definition args_A128____addstate_avx2 : seq var_i :=
  [:: st_60.(gv)
    ; AT_59.(gv)
    ; buf_90.(gv)
    ; offset_85.(gv)
    ; _LEN_53.(gv)
    ; _TRAILB_31.(gv) ].
Definition tyout_A128____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A128____addstate_avx2 : seq var_i :=
  [:: st_60.(gv); AT_59.(gv); offset_85.(gv) ].

(* Body *)
Definition body_A128____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_59.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_59) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_59.(gv)
                                                                ; Lvar _LEN_53.(gv)
                                                                ; Lvar _TRAILB_31.(gv)
                                                                ; Lvar AT_59.(gv)
                                                                ; Lvar r0_10.(gv) ] A128____a_ilen_read_bcast_upto8_at [:: Pvar buf_90
                                                                    ; Pvar offset_85
                                                                    ; Pvar DELTA_59
                                                                    ; Pvar _LEN_53
                                                                    ; Pvar _TRAILB_31
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_59 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_60.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_60 (Pconst (0)%Z)) (Pvar r0_10))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_59) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_53)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_31) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_59.(gv)
                                                                ; Lvar _LEN_53.(gv)
                                                                ; Lvar _TRAILB_31.(gv)
                                                                ; Lvar AT_59.(gv)
                                                                ; Lvar r1_10.(gv) ] A128____a_ilen_read_upto32_at [:: Pvar buf_90
                                                                    ; Pvar offset_85
                                                                    ; Pvar DELTA_59
                                                                    ; Pvar _LEN_53
                                                                    ; Pvar _TRAILB_31
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_59 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_60.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_60 (Pconst (1)%Z)) (Pvar r1_10))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_53)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_31) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_59.(gv)
                                                                ; Lvar _LEN_53.(gv)
                                                                ; Lvar _TRAILB_31.(gv)
                                                                ; Lvar AT_59.(gv)
                                                                ; Lvar t64_2_5.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_90
                                                                    ; Pvar offset_85
                                                                    ; Pvar DELTA_59
                                                                    ; Pvar _LEN_53
                                                                    ; Pvar _TRAILB_31
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_59 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_20.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_5)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_5.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_53)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_31) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_59.(gv)
                                                                  ; Lvar _LEN_53.(gv)
                                                                  ; Lvar _TRAILB_31.(gv)
                                                                  ; Lvar AT_59.(gv)
                                                                  ; Lvar r3_10.(gv) ] A128____a_ilen_read_upto32_at [:: Pvar buf_90
                                                                    ; Pvar offset_85
                                                                    ; Pvar DELTA_59
                                                                    ; Pvar _LEN_53
                                                                    ; Pvar _TRAILB_31
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_59 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_59.(gv)
                                                                  ; Lvar _LEN_53.(gv)
                                                                  ; Lvar _TRAILB_31.(gv)
                                                                  ; Lvar AT_59.(gv)
                                                                  ; Lvar t64_3_5.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_90
                                                                    ; Pvar offset_85
                                                                    ; Pvar DELTA_59
                                                                    ; Pvar _LEN_53
                                                                    ; Pvar _TRAILB_31
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_59 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_5.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_5)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_59.(gv)
                                                                  ; Lvar _LEN_53.(gv)
                                                                  ; Lvar _TRAILB_31.(gv)
                                                                  ; Lvar AT_59.(gv)
                                                                  ; Lvar r4_10.(gv) ] A128____a_ilen_read_upto32_at [:: Pvar buf_90
                                                                    ; Pvar offset_85
                                                                    ; Pvar DELTA_59
                                                                    ; Pvar _LEN_53
                                                                    ; Pvar _TRAILB_31
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_59 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_59.(gv)
                                                                  ; Lvar _LEN_53.(gv)
                                                                  ; Lvar _TRAILB_31.(gv)
                                                                  ; Lvar AT_59.(gv)
                                                                  ; Lvar t64_4_5.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_90
                                                                    ; Pvar offset_85
                                                                    ; Pvar DELTA_59
                                                                    ; Pvar _LEN_53
                                                                    ; Pvar _TRAILB_31
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_59 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_20.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_20
                                                                    ; Pvar t64_4_5
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_59.(gv)
                                                                  ; Lvar _LEN_53.(gv)
                                                                  ; Lvar _TRAILB_31.(gv)
                                                                  ; Lvar AT_59.(gv)
                                                                  ; Lvar r5_10.(gv) ] A128____a_ilen_read_upto32_at [:: Pvar buf_90
                                                                    ; Pvar offset_85
                                                                    ; Pvar DELTA_59
                                                                    ; Pvar _LEN_53
                                                                    ; Pvar _TRAILB_31
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_59 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_59.(gv)
                                                                  ; Lvar _LEN_53.(gv)
                                                                  ; Lvar _TRAILB_31.(gv)
                                                                  ; Lvar AT_59.(gv)
                                                                  ; Lvar t64_5_5.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_90
                                                                    ; Pvar offset_85
                                                                    ; Pvar DELTA_59
                                                                    ; Pvar _LEN_53
                                                                    ; Pvar _TRAILB_31
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_59 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_5
                                                                    ; Pvar t64_5_5
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_59.(gv)
                                                                  ; Lvar _LEN_53.(gv)
                                                                  ; Lvar _TRAILB_31.(gv)
                                                                  ; Lvar AT_59.(gv)
                                                                  ; Lvar r6_10.(gv) ] A128____a_ilen_read_upto32_at [:: Pvar buf_90
                                                                    ; Pvar offset_85
                                                                    ; Pvar DELTA_59
                                                                    ; Pvar _LEN_53
                                                                    ; Pvar _TRAILB_31
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_59 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_60.(gv) ] __addstate_r3456_avx2 [:: Pvar st_60
                                                                    ; Pvar r3_10
                                                                    ; Pvar r4_10
                                                                    ; Pvar r5_10
                                                                    ; Pvar r6_10 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_7.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_5)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_7.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_7
                                                                    ; Pvar t128_1_20
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_60.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_60 (Pconst (2)%Z)) (Pvar r2_7))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_85.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_85) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_59)))) ].

Definition fd_A128____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____addstate_avx2;
    f_params := args_A128____addstate_avx2;
    f_body := body_A128____addstate_avx2;
    f_tyout := tyout_A128____addstate_avx2;
    f_res := res_A128____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
