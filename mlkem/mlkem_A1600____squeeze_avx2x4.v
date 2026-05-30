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

(* A1600____squeeze_avx2x4 *)
(* Local variables *)
Definition st_109 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14750).
Definition buf0_38 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14751).
Definition buf1_38 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14752).
Definition buf2_38 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14753).
Definition buf3_38 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14754).
Definition _RATE8_50 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14755).
Definition offset_162 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14756).
Definition _LEN_102 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14757).
Definition ITERS_50 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14758).
Definition LO_19 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14759).
Definition i_66 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14760).

(* Signature *)
Definition tyin_A1600____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aint ].
Definition args_A1600____squeeze_avx2x4 : seq var_i :=
  [:: st_109.(gv)
    ; buf0_38.(gv)
    ; buf1_38.(gv)
    ; buf2_38.(gv)
    ; buf3_38.(gv)
    ; _RATE8_50.(gv) ].
Definition tyout_A1600____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 1600; aarr U8 1600; aarr U8 1600; aarr U8 1600 ].
Definition res_A1600____squeeze_avx2x4 : seq var_i :=
  [:: st_109.(gv); buf0_38.(gv); buf1_38.(gv); buf2_38.(gv); buf3_38.(gv) ].

(* Body *)
Definition body_A1600____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_162.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_102.(gv)) AT_none (aint) (Pconst (1600)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_50.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_102) (Pvar _RATE8_50)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_19.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_102) (Pvar _RATE8_50)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_50))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_66.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_66) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_50)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_109.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_109 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_38.(gv)
                                                                  ; Lvar buf1_38.(gv)
                                                                  ; Lvar buf2_38.(gv)
                                                                  ; Lvar buf3_38.(gv)
                                                                  ; Lvar offset_162.(gv) ] A1600____dumpstate_avx2x4 [:: Pvar buf0_38
                                                                    ; Pvar buf1_38
                                                                    ; Pvar buf2_38
                                                                    ; Pvar buf3_38
                                                                    ; Pvar offset_162
                                                                    ; Pvar _RATE8_50
                                                                    ; Pvar st_109 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_66.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_66) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_19))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_109.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_109 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_38.(gv)
                                                                ; Lvar buf1_38.(gv)
                                                                ; Lvar buf2_38.(gv)
                                                                ; Lvar buf3_38.(gv)
                                                                ; Lvar offset_162.(gv) ] A1600____dumpstate_avx2x4 [:: Pvar buf0_38
                                                                    ; Pvar buf1_38
                                                                    ; Pvar buf2_38
                                                                    ; Pvar buf3_38
                                                                    ; Pvar offset_162
                                                                    ; Pvar LO_19
                                                                    ; Pvar st_109 ]) ]
                              [::]) ].

Definition fd_A1600____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____squeeze_avx2x4;
    f_params := args_A1600____squeeze_avx2x4;
    f_body := body_A1600____squeeze_avx2x4;
    f_tyout := tyout_A1600____squeeze_avx2x4;
    f_res := res_A1600____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
