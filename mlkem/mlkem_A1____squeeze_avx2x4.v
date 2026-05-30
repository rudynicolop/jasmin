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

(* A1____squeeze_avx2x4 *)
(* Local variables *)
Definition st_25 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18053).
Definition buf0_6 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18054).
Definition buf1_6 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18055).
Definition buf2_6 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18056).
Definition buf3_6 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18057).
Definition _RATE8_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18058).
Definition offset_15 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18059).
Definition _LEN_18 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18060).
Definition ITERS_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18061).
Definition LO_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18062).
Definition i_16 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18063).

(* Signature *)
Definition tyin_A1____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 1; aarr U8 1; aarr U8 1; aarr U8 1; aint ].
Definition args_A1____squeeze_avx2x4 : seq var_i :=
  [:: st_25.(gv)
    ; buf0_6.(gv)
    ; buf1_6.(gv)
    ; buf2_6.(gv)
    ; buf3_6.(gv)
    ; _RATE8_8.(gv) ].
Definition tyout_A1____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 1; aarr U8 1; aarr U8 1; aarr U8 1 ].
Definition res_A1____squeeze_avx2x4 : seq var_i :=
  [:: st_25.(gv); buf0_6.(gv); buf1_6.(gv); buf2_6.(gv); buf3_6.(gv) ].

(* Body *)
Definition body_A1____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_15.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_18.(gv)) AT_none (aint) (Pconst (1)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_8.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18) (Pvar _RATE8_8)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_2.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18) (Pvar _RATE8_8)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_8))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_16.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_8)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_25.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_25 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_6.(gv)
                                                                  ; Lvar buf1_6.(gv)
                                                                  ; Lvar buf2_6.(gv)
                                                                  ; Lvar buf3_6.(gv)
                                                                  ; Lvar offset_15.(gv) ] A1____dumpstate_avx2x4 [:: Pvar buf0_6
                                                                    ; Pvar buf1_6
                                                                    ; Pvar buf2_6
                                                                    ; Pvar buf3_6
                                                                    ; Pvar offset_15
                                                                    ; Pvar _RATE8_8
                                                                    ; Pvar st_25 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_16.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_2))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_25.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_25 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_6.(gv)
                                                                ; Lvar buf1_6.(gv)
                                                                ; Lvar buf2_6.(gv)
                                                                ; Lvar buf3_6.(gv)
                                                                ; Lvar offset_15.(gv) ] A1____dumpstate_avx2x4 [:: Pvar buf0_6
                                                                    ; Pvar buf1_6
                                                                    ; Pvar buf2_6
                                                                    ; Pvar buf3_6
                                                                    ; Pvar offset_15
                                                                    ; Pvar LO_2
                                                                    ; Pvar st_25 ]) ]
                              [::]) ].

Definition fd_A1____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____squeeze_avx2x4;
    f_params := args_A1____squeeze_avx2x4;
    f_body := body_A1____squeeze_avx2x4;
    f_tyout := tyout_A1____squeeze_avx2x4;
    f_res := res_A1____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
