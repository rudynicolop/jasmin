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
Definition st_16278 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 16278).
Definition buf0_16279 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16279).
Definition buf1_16280 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16280).
Definition buf2_16281 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16281).
Definition buf3_16282 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16282).
Definition _RATE8_16283 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16283).
Definition offset_16284 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16284).
Definition _LEN_16285 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16285).
Definition ITERS_16286 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16286).
Definition LO_16287 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16287).
Definition i_16288 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16288).

(* Signature *)
Definition tyin_A128____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aint ].
Definition args_A128____squeeze_avx2x4 : seq var_i :=
  [:: st_16278.(gv)
    ; buf0_16279.(gv)
    ; buf1_16280.(gv)
    ; buf2_16281.(gv)
    ; buf3_16282.(gv)
    ; _RATE8_16283.(gv) ].
Definition tyout_A128____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 128; aarr U8 128; aarr U8 128; aarr U8 128 ].
Definition res_A128____squeeze_avx2x4 : seq var_i :=
  [:: st_16278.(gv)
    ; buf0_16279.(gv)
    ; buf1_16280.(gv)
    ; buf2_16281.(gv)
    ; buf3_16282.(gv) ].

(* Body *)
Definition body_A128____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_16284.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_16285.(gv)) AT_none (aint) (Pconst (128)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_16286.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16285) (Pvar _RATE8_16283)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_16287.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16285) (Pvar _RATE8_16283)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_16286))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_16288.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16288) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16286)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_16278.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_16278 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_16279.(gv)
                                                                  ; Lvar buf1_16280.(gv)
                                                                  ; Lvar buf2_16281.(gv)
                                                                  ; Lvar buf3_16282.(gv)
                                                                  ; Lvar offset_16284.(gv) ] A128____dumpstate_avx2x4 [:: Pvar buf0_16279
                                                                    ; Pvar buf1_16280
                                                                    ; Pvar buf2_16281
                                                                    ; Pvar buf3_16282
                                                                    ; Pvar offset_16284
                                                                    ; Pvar _RATE8_16283
                                                                    ; Pvar st_16278 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_16288.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16288) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_16287))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_16278.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_16278 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_16279.(gv)
                                                                ; Lvar buf1_16280.(gv)
                                                                ; Lvar buf2_16281.(gv)
                                                                ; Lvar buf3_16282.(gv)
                                                                ; Lvar offset_16284.(gv) ] A128____dumpstate_avx2x4 [:: Pvar buf0_16279
                                                                    ; Pvar buf1_16280
                                                                    ; Pvar buf2_16281
                                                                    ; Pvar buf3_16282
                                                                    ; Pvar offset_16284
                                                                    ; Pvar LO_16287
                                                                    ; Pvar st_16278 ]) ]
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
