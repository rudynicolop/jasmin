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

(* A128____squeeze_avx2x4 *)
(* Local variables *)
Definition st_69 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 16278).
Definition buf0_22 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16279).
Definition buf1_22 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16280).
Definition buf2_22 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16281).
Definition buf3_22 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16282).
Definition _RATE8_30 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16283).
Definition offset_94 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16284).
Definition _LEN_62 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16285).
Definition ITERS_30 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16286).
Definition LO_11 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16287).
Definition i_42 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16288).

(* Signature *)
Definition tyin_A128____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aint ].
Definition args_A128____squeeze_avx2x4 : seq var_i :=
  [:: st_69.(gv)
    ; buf0_22.(gv)
    ; buf1_22.(gv)
    ; buf2_22.(gv)
    ; buf3_22.(gv)
    ; _RATE8_30.(gv) ].
Definition tyout_A128____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 128; aarr U8 128; aarr U8 128; aarr U8 128 ].
Definition res_A128____squeeze_avx2x4 : seq var_i :=
  [:: st_69.(gv); buf0_22.(gv); buf1_22.(gv); buf2_22.(gv); buf3_22.(gv) ].

(* Body *)
Definition body_A128____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_94.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_62.(gv)) AT_none (aint) (Pconst (128)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_30.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_62) (Pvar _RATE8_30)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_11.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_62) (Pvar _RATE8_30)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_30))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_42.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_42) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_30)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_69.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_69 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_22.(gv)
                                                                  ; Lvar buf1_22.(gv)
                                                                  ; Lvar buf2_22.(gv)
                                                                  ; Lvar buf3_22.(gv)
                                                                  ; Lvar offset_94.(gv) ] A128____dumpstate_avx2x4 [:: Pvar buf0_22
                                                                    ; Pvar buf1_22
                                                                    ; Pvar buf2_22
                                                                    ; Pvar buf3_22
                                                                    ; Pvar offset_94
                                                                    ; Pvar _RATE8_30
                                                                    ; Pvar st_69 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_42.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_42) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_11))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_69.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_69 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_22.(gv)
                                                                ; Lvar buf1_22.(gv)
                                                                ; Lvar buf2_22.(gv)
                                                                ; Lvar buf3_22.(gv)
                                                                ; Lvar offset_94.(gv) ] A128____dumpstate_avx2x4 [:: Pvar buf0_22
                                                                    ; Pvar buf1_22
                                                                    ; Pvar buf2_22
                                                                    ; Pvar buf3_22
                                                                    ; Pvar offset_94
                                                                    ; Pvar LO_11
                                                                    ; Pvar st_69 ]) ]
                              [::]) ].

Definition fd_A128____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____squeeze_avx2x4;
    f_params := args_A128____squeeze_avx2x4;
    f_body := body_A128____squeeze_avx2x4;
    f_tyout := tyout_A128____squeeze_avx2x4;
    f_res := res_A128____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
