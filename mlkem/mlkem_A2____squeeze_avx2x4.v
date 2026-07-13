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

(* A2____squeeze_avx2x4 *)
(* Local variables *)
Definition st_35 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17671).
Definition buf0_10 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17672).
Definition buf1_10 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17673).
Definition buf2_10 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17674).
Definition buf3_10 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17675).
Definition _RATE8_13 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17676).
Definition offset_32 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17677).
Definition _LEN_28 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17678).
Definition ITERS_13 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17679).
Definition LO_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17680).
Definition i_22 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17681).

(* Signature *)
Definition tyin_A2____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 2; aarr U8 2; aarr U8 2; aarr U8 2; aint ].
Definition args_A2____squeeze_avx2x4 : seq var_i :=
  [:: st_35.(gv)
    ; buf0_10.(gv)
    ; buf1_10.(gv)
    ; buf2_10.(gv)
    ; buf3_10.(gv)
    ; _RATE8_13.(gv) ].
Definition tyout_A2____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 2; aarr U8 2; aarr U8 2; aarr U8 2 ].
Definition res_A2____squeeze_avx2x4 : seq var_i :=
  [:: st_35.(gv); buf0_10.(gv); buf1_10.(gv); buf2_10.(gv); buf3_10.(gv) ].

(* Body *)
Definition body_A2____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_32.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_28.(gv)) AT_none (aint) (Pconst (2)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_13.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_28) (Pvar _RATE8_13)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_4.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_28) (Pvar _RATE8_13)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_13))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_22.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_22) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_13)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_35.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_35 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_10.(gv)
                                                                  ; Lvar buf1_10.(gv)
                                                                  ; Lvar buf2_10.(gv)
                                                                  ; Lvar buf3_10.(gv)
                                                                  ; Lvar offset_32.(gv) ] A2____dumpstate_avx2x4 [:: Pvar buf0_10
                                                                    ; Pvar buf1_10
                                                                    ; Pvar buf2_10
                                                                    ; Pvar buf3_10
                                                                    ; Pvar offset_32
                                                                    ; Pvar _RATE8_13
                                                                    ; Pvar st_35 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_22.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_22) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_4))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_35.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_35 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_10.(gv)
                                                                ; Lvar buf1_10.(gv)
                                                                ; Lvar buf2_10.(gv)
                                                                ; Lvar buf3_10.(gv)
                                                                ; Lvar offset_32.(gv) ] A2____dumpstate_avx2x4 [:: Pvar buf0_10
                                                                    ; Pvar buf1_10
                                                                    ; Pvar buf2_10
                                                                    ; Pvar buf3_10
                                                                    ; Pvar offset_32
                                                                    ; Pvar LO_4
                                                                    ; Pvar st_35 ]) ]
                              [::]) ].

Definition fd_A2____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____squeeze_avx2x4;
    f_params := args_A2____squeeze_avx2x4;
    f_body := body_A2____squeeze_avx2x4;
    f_tyout := tyout_A2____squeeze_avx2x4;
    f_res := res_A2____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
