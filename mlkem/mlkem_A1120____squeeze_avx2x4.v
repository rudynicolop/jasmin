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
Definition st_15132 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15132).
Definition buf0_15133 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15133).
Definition buf1_15134 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15134).
Definition buf2_15135 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15135).
Definition buf3_15136 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15136).
Definition _RATE8_15137 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15137).
Definition offset_15138 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15138).
Definition _LEN_15139 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15139).
Definition ITERS_15140 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15140).
Definition LO_15141 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15141).
Definition i_15142 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15142).

(* Signature *)
Definition tyin_A1120____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aint ].
Definition args_A1120____squeeze_avx2x4 : seq var_i :=
  [:: st_15132.(gv)
    ; buf0_15133.(gv)
    ; buf1_15134.(gv)
    ; buf2_15135.(gv)
    ; buf3_15136.(gv)
    ; _RATE8_15137.(gv) ].
Definition tyout_A1120____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 1120; aarr U8 1120; aarr U8 1120; aarr U8 1120 ].
Definition res_A1120____squeeze_avx2x4 : seq var_i :=
  [:: st_15132.(gv)
    ; buf0_15133.(gv)
    ; buf1_15134.(gv)
    ; buf2_15135.(gv)
    ; buf3_15136.(gv) ].

(* Body *)
Definition body_A1120____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_15138.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15139.(gv)) AT_none (aint) (Pconst (1120)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_15140.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15139) (Pvar _RATE8_15137)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_15141.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15139) (Pvar _RATE8_15137)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_15140))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_15142.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15142) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_15140)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_15132.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15132 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_15133.(gv)
                                                                  ; Lvar buf1_15134.(gv)
                                                                  ; Lvar buf2_15135.(gv)
                                                                  ; Lvar buf3_15136.(gv)
                                                                  ; Lvar offset_15138.(gv) ] A1120____dumpstate_avx2x4 [:: Pvar buf0_15133
                                                                    ; Pvar buf1_15134
                                                                    ; Pvar buf2_15135
                                                                    ; Pvar buf3_15136
                                                                    ; Pvar offset_15138
                                                                    ; Pvar _RATE8_15137
                                                                    ; Pvar st_15132 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_15142.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15142) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_15141))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_15132.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15132 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_15133.(gv)
                                                                ; Lvar buf1_15134.(gv)
                                                                ; Lvar buf2_15135.(gv)
                                                                ; Lvar buf3_15136.(gv)
                                                                ; Lvar offset_15138.(gv) ] A1120____dumpstate_avx2x4 [:: Pvar buf0_15133
                                                                    ; Pvar buf1_15134
                                                                    ; Pvar buf2_15135
                                                                    ; Pvar buf3_15136
                                                                    ; Pvar offset_15138
                                                                    ; Pvar LO_15141
                                                                    ; Pvar st_15132 ]) ]
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
