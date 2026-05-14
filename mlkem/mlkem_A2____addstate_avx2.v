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
Definition st_17854 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 17854).
Definition AT_17855 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17855).
Definition buf_17856 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17856).
Definition offset_17857 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17857).
Definition _LEN_17858 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17858).
Definition _TRAILB_17859 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17859).
Definition DELTA_17860 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17860).
Definition r0_17861 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17861).
Definition r1_17862 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17862).
Definition t64_2_17863 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17863).
Definition t128_1_17864 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17864).
Definition t128_2_17865 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17865).
Definition r3_17866 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17866).
Definition t64_3_17867 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17867).
Definition r4_17868 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17868).
Definition t64_4_17869 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17869).
Definition r5_17870 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17870).
Definition t64_5_17871 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17871).
Definition r6_17872 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17872).
Definition r2_17873 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17873).

(* Signature *)
Definition tyin_A2____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 2; aword U64; aint; aint ].
Definition args_A2____addstate_avx2 : seq var_i :=
  [:: st_17854.(gv)
    ; AT_17855.(gv)
    ; buf_17856.(gv)
    ; offset_17857.(gv)
    ; _LEN_17858.(gv)
    ; _TRAILB_17859.(gv) ].
Definition tyout_A2____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A2____addstate_avx2 : seq var_i :=
  [:: st_17854.(gv); AT_17855.(gv); offset_17857.(gv) ].

(* Body *)
Definition body_A2____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_17860.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_17855) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17860.(gv)
                                                                ; Lvar _LEN_17858.(gv)
                                                                ; Lvar _TRAILB_17859.(gv)
                                                                ; Lvar AT_17855.(gv)
                                                                ; Lvar r0_17861.(gv) ] A2____a_ilen_read_bcast_upto8_at [:: Pvar buf_17856
                                                                    ; Pvar offset_17857
                                                                    ; Pvar DELTA_17860
                                                                    ; Pvar _LEN_17858
                                                                    ; Pvar _TRAILB_17859
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_17855 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_17854.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_17854 (Pconst (0)%Z)) (Pvar r0_17861))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_17855) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17858)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17859) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17860.(gv)
                                                                ; Lvar _LEN_17858.(gv)
                                                                ; Lvar _TRAILB_17859.(gv)
                                                                ; Lvar AT_17855.(gv)
                                                                ; Lvar r1_17862.(gv) ] A2____a_ilen_read_upto32_at [:: Pvar buf_17856
                                                                    ; Pvar offset_17857
                                                                    ; Pvar DELTA_17860
                                                                    ; Pvar _LEN_17858
                                                                    ; Pvar _TRAILB_17859
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_17855 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_17854.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_17854 (Pconst (1)%Z)) (Pvar r1_17862))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17858)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17859) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17860.(gv)
                                                                ; Lvar _LEN_17858.(gv)
                                                                ; Lvar _TRAILB_17859.(gv)
                                                                ; Lvar AT_17855.(gv)
                                                                ; Lvar t64_2_17863.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_17856
                                                                    ; Pvar offset_17857
                                                                    ; Pvar DELTA_17860
                                                                    ; Pvar _LEN_17858
                                                                    ; Pvar _TRAILB_17859
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_17855 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_17864.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_17863)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_17865.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17858)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17859) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17860.(gv)
                                                                  ; Lvar _LEN_17858.(gv)
                                                                  ; Lvar _TRAILB_17859.(gv)
                                                                  ; Lvar AT_17855.(gv)
                                                                  ; Lvar r3_17866.(gv) ] A2____a_ilen_read_upto32_at [:: Pvar buf_17856
                                                                    ; Pvar offset_17857
                                                                    ; Pvar DELTA_17860
                                                                    ; Pvar _LEN_17858
                                                                    ; Pvar _TRAILB_17859
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_17855 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17860.(gv)
                                                                  ; Lvar _LEN_17858.(gv)
                                                                  ; Lvar _TRAILB_17859.(gv)
                                                                  ; Lvar AT_17855.(gv)
                                                                  ; Lvar t64_3_17867.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_17856
                                                                    ; Pvar offset_17857
                                                                    ; Pvar DELTA_17860
                                                                    ; Pvar _LEN_17858
                                                                    ; Pvar _TRAILB_17859
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_17855 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_17865.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_17867)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17860.(gv)
                                                                  ; Lvar _LEN_17858.(gv)
                                                                  ; Lvar _TRAILB_17859.(gv)
                                                                  ; Lvar AT_17855.(gv)
                                                                  ; Lvar r4_17868.(gv) ] A2____a_ilen_read_upto32_at [:: Pvar buf_17856
                                                                    ; Pvar offset_17857
                                                                    ; Pvar DELTA_17860
                                                                    ; Pvar _LEN_17858
                                                                    ; Pvar _TRAILB_17859
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_17855 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17860.(gv)
                                                                  ; Lvar _LEN_17858.(gv)
                                                                  ; Lvar _TRAILB_17859.(gv)
                                                                  ; Lvar AT_17855.(gv)
                                                                  ; Lvar t64_4_17869.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_17856
                                                                    ; Pvar offset_17857
                                                                    ; Pvar DELTA_17860
                                                                    ; Pvar _LEN_17858
                                                                    ; Pvar _TRAILB_17859
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_17855 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_17864.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_17864
                                                                    ; Pvar t64_4_17869
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17860.(gv)
                                                                  ; Lvar _LEN_17858.(gv)
                                                                  ; Lvar _TRAILB_17859.(gv)
                                                                  ; Lvar AT_17855.(gv)
                                                                  ; Lvar r5_17870.(gv) ] A2____a_ilen_read_upto32_at [:: Pvar buf_17856
                                                                    ; Pvar offset_17857
                                                                    ; Pvar DELTA_17860
                                                                    ; Pvar _LEN_17858
                                                                    ; Pvar _TRAILB_17859
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_17855 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17860.(gv)
                                                                  ; Lvar _LEN_17858.(gv)
                                                                  ; Lvar _TRAILB_17859.(gv)
                                                                  ; Lvar AT_17855.(gv)
                                                                  ; Lvar t64_5_17871.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_17856
                                                                    ; Pvar offset_17857
                                                                    ; Pvar DELTA_17860
                                                                    ; Pvar _LEN_17858
                                                                    ; Pvar _TRAILB_17859
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_17855 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_17865.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_17865
                                                                    ; Pvar t64_5_17871
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17860.(gv)
                                                                  ; Lvar _LEN_17858.(gv)
                                                                  ; Lvar _TRAILB_17859.(gv)
                                                                  ; Lvar AT_17855.(gv)
                                                                  ; Lvar r6_17872.(gv) ] A2____a_ilen_read_upto32_at [:: Pvar buf_17856
                                                                    ; Pvar offset_17857
                                                                    ; Pvar DELTA_17860
                                                                    ; Pvar _LEN_17858
                                                                    ; Pvar _TRAILB_17859
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_17855 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_17854.(gv) ] __addstate_r3456_avx2 [:: Pvar st_17854
                                                                    ; Pvar r3_17866
                                                                    ; Pvar r4_17868
                                                                    ; Pvar r5_17870
                                                                    ; Pvar r6_17872 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_17873.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_17865)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_17873.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_17873
                                                                    ; Pvar t128_1_17864
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_17854.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_17854 (Pconst (2)%Z)) (Pvar r2_17873))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_17857.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17857) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17860)))) ].

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
