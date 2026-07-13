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

(* A1120____squeeze_avx2x4 *)
(* Local variables *)
Definition st_99 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15132).
Definition buf0_34 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15133).
Definition buf1_34 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15134).
Definition buf2_34 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15135).
Definition buf3_34 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15136).
Definition _RATE8_45 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15137).
Definition offset_145 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15138).
Definition _LEN_92 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15139).
Definition ITERS_45 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15140).
Definition LO_17 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15141).
Definition i_60 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15142).

(* Signature *)
Definition tyin_A1120____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aint ].
Definition args_A1120____squeeze_avx2x4 : seq var_i :=
  [:: st_99.(gv)
    ; buf0_34.(gv)
    ; buf1_34.(gv)
    ; buf2_34.(gv)
    ; buf3_34.(gv)
    ; _RATE8_45.(gv) ].
Definition tyout_A1120____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 1120; aarr U8 1120; aarr U8 1120; aarr U8 1120 ].
Definition res_A1120____squeeze_avx2x4 : seq var_i :=
  [:: st_99.(gv); buf0_34.(gv); buf1_34.(gv); buf2_34.(gv); buf3_34.(gv) ].

(* Body *)
Definition body_A1120____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_145.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_92.(gv)) AT_none (aint) (Pconst (1120)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_45.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_92) (Pvar _RATE8_45)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_17.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_92) (Pvar _RATE8_45)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_45))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_60.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_60) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_45)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_99.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_99 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_34.(gv)
                                                                  ; Lvar buf1_34.(gv)
                                                                  ; Lvar buf2_34.(gv)
                                                                  ; Lvar buf3_34.(gv)
                                                                  ; Lvar offset_145.(gv) ] A1120____dumpstate_avx2x4 [:: Pvar buf0_34
                                                                    ; Pvar buf1_34
                                                                    ; Pvar buf2_34
                                                                    ; Pvar buf3_34
                                                                    ; Pvar offset_145
                                                                    ; Pvar _RATE8_45
                                                                    ; Pvar st_99 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_60.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_60) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_17))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_99.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_99 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_34.(gv)
                                                                ; Lvar buf1_34.(gv)
                                                                ; Lvar buf2_34.(gv)
                                                                ; Lvar buf3_34.(gv)
                                                                ; Lvar offset_145.(gv) ] A1120____dumpstate_avx2x4 [:: Pvar buf0_34
                                                                    ; Pvar buf1_34
                                                                    ; Pvar buf2_34
                                                                    ; Pvar buf3_34
                                                                    ; Pvar offset_145
                                                                    ; Pvar LO_17
                                                                    ; Pvar st_99 ]) ]
                              [::]) ].

Definition fd_A1120____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____squeeze_avx2x4;
    f_params := args_A1120____squeeze_avx2x4;
    f_body := body_A1120____squeeze_avx2x4;
    f_tyout := tyout_A1120____squeeze_avx2x4;
    f_res := res_A1120____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
