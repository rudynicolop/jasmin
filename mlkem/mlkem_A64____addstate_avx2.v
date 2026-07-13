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

(* A64____addstate_avx2 *)
(* Local variables *)
Definition st_56 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16708).
Definition AT_53 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16709).
Definition buf_78 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16710).
Definition offset_74 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16711).
Definition _LEN_49 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16712).
Definition _TRAILB_29 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16713).
Definition DELTA_50 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16714).
Definition r0_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16715).
Definition r1_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16716).
Definition t64_2_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16717).
Definition t128_1_17 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16718).
Definition t128_2_4 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16719).
Definition r3_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16720).
Definition t64_3_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16721).
Definition r4_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16722).
Definition t64_4_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16723).
Definition r5_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16724).
Definition t64_5_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16725).
Definition r6_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16726).
Definition r2_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16727).

(* Signature *)
Definition tyin_A64____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 64; aword U64; aint; aint ].
Definition args_A64____addstate_avx2 : seq var_i :=
  [:: st_56.(gv)
    ; AT_53.(gv)
    ; buf_78.(gv)
    ; offset_74.(gv)
    ; _LEN_49.(gv)
    ; _TRAILB_29.(gv) ].
Definition tyout_A64____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_A64____addstate_avx2 : seq var_i :=
  [:: st_56.(gv); AT_53.(gv); offset_74.(gv) ].

(* Body *)
Definition body_A64____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_50.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_53) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_50.(gv)
                                                                ; Lvar _LEN_49.(gv)
                                                                ; Lvar _TRAILB_29.(gv)
                                                                ; Lvar AT_53.(gv)
                                                                ; Lvar r0_9.(gv) ] A64____a_ilen_read_bcast_upto8_at [:: Pvar buf_78
                                                                    ; Pvar offset_74
                                                                    ; Pvar DELTA_50
                                                                    ; Pvar _LEN_49
                                                                    ; Pvar _TRAILB_29
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_53 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_56.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_56 (Pconst (0)%Z)) (Pvar r0_9))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_53) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_49)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_29) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_50.(gv)
                                                                ; Lvar _LEN_49.(gv)
                                                                ; Lvar _TRAILB_29.(gv)
                                                                ; Lvar AT_53.(gv)
                                                                ; Lvar r1_9.(gv) ] A64____a_ilen_read_upto32_at [:: Pvar buf_78
                                                                    ; Pvar offset_74
                                                                    ; Pvar DELTA_50
                                                                    ; Pvar _LEN_49
                                                                    ; Pvar _TRAILB_29
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_53 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_56.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_56 (Pconst (1)%Z)) (Pvar r1_9))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_49)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_29) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_50.(gv)
                                                                ; Lvar _LEN_49.(gv)
                                                                ; Lvar _TRAILB_29.(gv)
                                                                ; Lvar AT_53.(gv)
                                                                ; Lvar t64_2_4.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_78
                                                                    ; Pvar offset_74
                                                                    ; Pvar DELTA_50
                                                                    ; Pvar _LEN_49
                                                                    ; Pvar _TRAILB_29
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_53 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_17.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_4)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_4.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_49)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_29) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_50.(gv)
                                                                  ; Lvar _LEN_49.(gv)
                                                                  ; Lvar _TRAILB_29.(gv)
                                                                  ; Lvar AT_53.(gv)
                                                                  ; Lvar r3_9.(gv) ] A64____a_ilen_read_upto32_at [:: Pvar buf_78
                                                                    ; Pvar offset_74
                                                                    ; Pvar DELTA_50
                                                                    ; Pvar _LEN_49
                                                                    ; Pvar _TRAILB_29
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_53 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_50.(gv)
                                                                  ; Lvar _LEN_49.(gv)
                                                                  ; Lvar _TRAILB_29.(gv)
                                                                  ; Lvar AT_53.(gv)
                                                                  ; Lvar t64_3_4.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_78
                                                                    ; Pvar offset_74
                                                                    ; Pvar DELTA_50
                                                                    ; Pvar _LEN_49
                                                                    ; Pvar _TRAILB_29
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_53 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_4.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_4)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_50.(gv)
                                                                  ; Lvar _LEN_49.(gv)
                                                                  ; Lvar _TRAILB_29.(gv)
                                                                  ; Lvar AT_53.(gv)
                                                                  ; Lvar r4_9.(gv) ] A64____a_ilen_read_upto32_at [:: Pvar buf_78
                                                                    ; Pvar offset_74
                                                                    ; Pvar DELTA_50
                                                                    ; Pvar _LEN_49
                                                                    ; Pvar _TRAILB_29
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_53 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_50.(gv)
                                                                  ; Lvar _LEN_49.(gv)
                                                                  ; Lvar _TRAILB_29.(gv)
                                                                  ; Lvar AT_53.(gv)
                                                                  ; Lvar t64_4_4.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_78
                                                                    ; Pvar offset_74
                                                                    ; Pvar DELTA_50
                                                                    ; Pvar _LEN_49
                                                                    ; Pvar _TRAILB_29
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_53 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_17.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_17
                                                                    ; Pvar t64_4_4
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_50.(gv)
                                                                  ; Lvar _LEN_49.(gv)
                                                                  ; Lvar _TRAILB_29.(gv)
                                                                  ; Lvar AT_53.(gv)
                                                                  ; Lvar r5_9.(gv) ] A64____a_ilen_read_upto32_at [:: Pvar buf_78
                                                                    ; Pvar offset_74
                                                                    ; Pvar DELTA_50
                                                                    ; Pvar _LEN_49
                                                                    ; Pvar _TRAILB_29
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_53 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_50.(gv)
                                                                  ; Lvar _LEN_49.(gv)
                                                                  ; Lvar _TRAILB_29.(gv)
                                                                  ; Lvar AT_53.(gv)
                                                                  ; Lvar t64_5_4.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_78
                                                                    ; Pvar offset_74
                                                                    ; Pvar DELTA_50
                                                                    ; Pvar _LEN_49
                                                                    ; Pvar _TRAILB_29
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_53 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_4
                                                                    ; Pvar t64_5_4
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_50.(gv)
                                                                  ; Lvar _LEN_49.(gv)
                                                                  ; Lvar _TRAILB_29.(gv)
                                                                  ; Lvar AT_53.(gv)
                                                                  ; Lvar r6_9.(gv) ] A64____a_ilen_read_upto32_at [:: Pvar buf_78
                                                                    ; Pvar offset_74
                                                                    ; Pvar DELTA_50
                                                                    ; Pvar _LEN_49
                                                                    ; Pvar _TRAILB_29
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_53 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_56.(gv) ] __addstate_r3456_avx2 [:: Pvar st_56
                                                                    ; Pvar r3_9
                                                                    ; Pvar r4_9
                                                                    ; Pvar r5_9
                                                                    ; Pvar r6_9 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_6.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_4)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_6.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_6
                                                                    ; Pvar t128_1_17
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_56.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_56 (Pconst (2)%Z)) (Pvar r2_6))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_74.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_74) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_50)))) ].

Definition fd_A64____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____addstate_avx2;
    f_params := args_A64____addstate_avx2;
    f_body := body_A64____addstate_avx2;
    f_tyout := tyout_A64____addstate_avx2;
    f_res := res_A64____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
