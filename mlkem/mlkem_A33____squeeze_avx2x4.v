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

(* A33____squeeze_avx2x4 *)
(* Local variables *)
Definition st_55 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 16907).
Definition buf0_18 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16908).
Definition buf1_18 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16909).
Definition buf2_18 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16910).
Definition buf3_18 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16911).
Definition _RATE8_23 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16912).
Definition offset_66 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16913).
Definition _LEN_48 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16914).
Definition ITERS_23 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16915).
Definition LO_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16916).
Definition i_34 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16917).

(* Signature *)
Definition tyin_A33____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 33; aarr U8 33; aarr U8 33; aarr U8 33; aint ].
Definition args_A33____squeeze_avx2x4 : seq var_i :=
  [:: st_55.(gv)
    ; buf0_18.(gv)
    ; buf1_18.(gv)
    ; buf2_18.(gv)
    ; buf3_18.(gv)
    ; _RATE8_23.(gv) ].
Definition tyout_A33____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 33; aarr U8 33; aarr U8 33; aarr U8 33 ].
Definition res_A33____squeeze_avx2x4 : seq var_i :=
  [:: st_55.(gv); buf0_18.(gv); buf1_18.(gv); buf2_18.(gv); buf3_18.(gv) ].

(* Body *)
Definition body_A33____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_66.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_48.(gv)) AT_none (aint) (Pconst (33)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_23.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_48) (Pvar _RATE8_23)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_8.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_48) (Pvar _RATE8_23)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_23))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_34.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_34) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_23)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_55.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_55 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_18.(gv)
                                                                  ; Lvar buf1_18.(gv)
                                                                  ; Lvar buf2_18.(gv)
                                                                  ; Lvar buf3_18.(gv)
                                                                  ; Lvar offset_66.(gv) ] A33____dumpstate_avx2x4 [:: Pvar buf0_18
                                                                    ; Pvar buf1_18
                                                                    ; Pvar buf2_18
                                                                    ; Pvar buf3_18
                                                                    ; Pvar offset_66
                                                                    ; Pvar _RATE8_23
                                                                    ; Pvar st_55 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_34.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_34) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_8))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_55.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_55 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_18.(gv)
                                                                ; Lvar buf1_18.(gv)
                                                                ; Lvar buf2_18.(gv)
                                                                ; Lvar buf3_18.(gv)
                                                                ; Lvar offset_66.(gv) ] A33____dumpstate_avx2x4 [:: Pvar buf0_18
                                                                    ; Pvar buf1_18
                                                                    ; Pvar buf2_18
                                                                    ; Pvar buf3_18
                                                                    ; Pvar offset_66
                                                                    ; Pvar LO_8
                                                                    ; Pvar st_55 ]) ]
                              [::]) ].

Definition fd_A33____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____squeeze_avx2x4;
    f_params := args_A33____squeeze_avx2x4;
    f_body := body_A33____squeeze_avx2x4;
    f_tyout := tyout_A33____squeeze_avx2x4;
    f_res := res_A33____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
