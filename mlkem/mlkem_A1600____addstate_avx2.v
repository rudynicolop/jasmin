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
Definition st_14933 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 14933).
Definition AT_14934 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14934).
Definition buf_14935 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14935).
Definition offset_14936 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14936).
Definition _LEN_14937 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14937).
Definition _TRAILB_14938 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14938).
Definition DELTA_14939 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14939).
Definition r0_14940 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14940).
Definition r1_14941 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14941).
Definition t64_2_14942 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14942).
Definition t128_1_14943 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14943).
Definition t128_2_14944 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14944).
Definition r3_14945 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14945).
Definition t64_3_14946 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14946).
Definition r4_14947 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14947).
Definition t64_4_14948 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14948).
Definition r5_14949 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14949).
Definition t64_5_14950 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14950).
Definition r6_14951 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14951).
Definition r2_14952 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14952).

(* Signature *)
Definition tyin_A1600____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1600; aword U64; aint; aint ].
Definition args_A1600____addstate_avx2 : seq var_i :=
  [:: st_14933.(gv)
    ; AT_14934.(gv)
    ; buf_14935.(gv)
    ; offset_14936.(gv)
    ; _LEN_14937.(gv)
    ; _TRAILB_14938.(gv) ].
Definition tyout_A1600____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A1600____addstate_avx2 : seq var_i :=
  [:: st_14933.(gv); AT_14934.(gv); offset_14936.(gv) ].

(* Body *)
Definition body_A1600____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_14939.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_14934) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_14939.(gv)
                                                                ; Lvar _LEN_14937.(gv)
                                                                ; Lvar _TRAILB_14938.(gv)
                                                                ; Lvar AT_14934.(gv)
                                                                ; Lvar r0_14940.(gv) ] A1600____a_ilen_read_bcast_upto8_at [:: Pvar buf_14935
                                                                    ; Pvar offset_14936
                                                                    ; Pvar DELTA_14939
                                                                    ; Pvar _LEN_14937
                                                                    ; Pvar _TRAILB_14938
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_14934 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_14933.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_14933 (Pconst (0)%Z)) (Pvar r0_14940))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_14934) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14937)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14938) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_14939.(gv)
                                                                ; Lvar _LEN_14937.(gv)
                                                                ; Lvar _TRAILB_14938.(gv)
                                                                ; Lvar AT_14934.(gv)
                                                                ; Lvar r1_14941.(gv) ] A1600____a_ilen_read_upto32_at [:: Pvar buf_14935
                                                                    ; Pvar offset_14936
                                                                    ; Pvar DELTA_14939
                                                                    ; Pvar _LEN_14937
                                                                    ; Pvar _TRAILB_14938
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_14934 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_14933.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_14933 (Pconst (1)%Z)) (Pvar r1_14941))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14937)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14938) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_14939.(gv)
                                                                ; Lvar _LEN_14937.(gv)
                                                                ; Lvar _TRAILB_14938.(gv)
                                                                ; Lvar AT_14934.(gv)
                                                                ; Lvar t64_2_14942.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_14935
                                                                    ; Pvar offset_14936
                                                                    ; Pvar DELTA_14939
                                                                    ; Pvar _LEN_14937
                                                                    ; Pvar _TRAILB_14938
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_14934 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_14943.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_14942)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_14944.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14937)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14938) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14939.(gv)
                                                                  ; Lvar _LEN_14937.(gv)
                                                                  ; Lvar _TRAILB_14938.(gv)
                                                                  ; Lvar AT_14934.(gv)
                                                                  ; Lvar r3_14945.(gv) ] A1600____a_ilen_read_upto32_at [:: Pvar buf_14935
                                                                    ; Pvar offset_14936
                                                                    ; Pvar DELTA_14939
                                                                    ; Pvar _LEN_14937
                                                                    ; Pvar _TRAILB_14938
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_14934 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14939.(gv)
                                                                  ; Lvar _LEN_14937.(gv)
                                                                  ; Lvar _TRAILB_14938.(gv)
                                                                  ; Lvar AT_14934.(gv)
                                                                  ; Lvar t64_3_14946.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_14935
                                                                    ; Pvar offset_14936
                                                                    ; Pvar DELTA_14939
                                                                    ; Pvar _LEN_14937
                                                                    ; Pvar _TRAILB_14938
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_14934 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_14944.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_14946)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14939.(gv)
                                                                  ; Lvar _LEN_14937.(gv)
                                                                  ; Lvar _TRAILB_14938.(gv)
                                                                  ; Lvar AT_14934.(gv)
                                                                  ; Lvar r4_14947.(gv) ] A1600____a_ilen_read_upto32_at [:: Pvar buf_14935
                                                                    ; Pvar offset_14936
                                                                    ; Pvar DELTA_14939
                                                                    ; Pvar _LEN_14937
                                                                    ; Pvar _TRAILB_14938
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_14934 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14939.(gv)
                                                                  ; Lvar _LEN_14937.(gv)
                                                                  ; Lvar _TRAILB_14938.(gv)
                                                                  ; Lvar AT_14934.(gv)
                                                                  ; Lvar t64_4_14948.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_14935
                                                                    ; Pvar offset_14936
                                                                    ; Pvar DELTA_14939
                                                                    ; Pvar _LEN_14937
                                                                    ; Pvar _TRAILB_14938
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_14934 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_14943.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_14943
                                                                    ; Pvar t64_4_14948
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14939.(gv)
                                                                  ; Lvar _LEN_14937.(gv)
                                                                  ; Lvar _TRAILB_14938.(gv)
                                                                  ; Lvar AT_14934.(gv)
                                                                  ; Lvar r5_14949.(gv) ] A1600____a_ilen_read_upto32_at [:: Pvar buf_14935
                                                                    ; Pvar offset_14936
                                                                    ; Pvar DELTA_14939
                                                                    ; Pvar _LEN_14937
                                                                    ; Pvar _TRAILB_14938
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_14934 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14939.(gv)
                                                                  ; Lvar _LEN_14937.(gv)
                                                                  ; Lvar _TRAILB_14938.(gv)
                                                                  ; Lvar AT_14934.(gv)
                                                                  ; Lvar t64_5_14950.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_14935
                                                                    ; Pvar offset_14936
                                                                    ; Pvar DELTA_14939
                                                                    ; Pvar _LEN_14937
                                                                    ; Pvar _TRAILB_14938
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_14934 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_14944.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_14944
                                                                    ; Pvar t64_5_14950
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14939.(gv)
                                                                  ; Lvar _LEN_14937.(gv)
                                                                  ; Lvar _TRAILB_14938.(gv)
                                                                  ; Lvar AT_14934.(gv)
                                                                  ; Lvar r6_14951.(gv) ] A1600____a_ilen_read_upto32_at [:: Pvar buf_14935
                                                                    ; Pvar offset_14936
                                                                    ; Pvar DELTA_14939
                                                                    ; Pvar _LEN_14937
                                                                    ; Pvar _TRAILB_14938
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_14934 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_14933.(gv) ] __addstate_r3456_avx2 [:: Pvar st_14933
                                                                    ; Pvar r3_14945
                                                                    ; Pvar r4_14947
                                                                    ; Pvar r5_14949
                                                                    ; Pvar r6_14951 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_14952.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_14944)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_14952.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_14952
                                                                    ; Pvar t128_1_14943
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_14933.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_14933 (Pconst (2)%Z)) (Pvar r2_14952))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_14936.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14936) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14939)))) ].

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
