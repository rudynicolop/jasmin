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
Definition st_17671 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17671).
Definition buf0_17672 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17672).
Definition buf1_17673 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17673).
Definition buf2_17674 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17674).
Definition buf3_17675 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17675).
Definition _RATE8_17676 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17676).
Definition offset_17677 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17677).
Definition _LEN_17678 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17678).
Definition ITERS_17679 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17679).
Definition LO_17680 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17680).
Definition i_17681 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17681).

(* Signature *)
Definition tyin_A2____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 2; aarr U8 2; aarr U8 2; aarr U8 2; aint ].
Definition args_A2____squeeze_avx2x4 : seq var_i :=
  [:: st_17671.(gv)
    ; buf0_17672.(gv)
    ; buf1_17673.(gv)
    ; buf2_17674.(gv)
    ; buf3_17675.(gv)
    ; _RATE8_17676.(gv) ].
Definition tyout_A2____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 2; aarr U8 2; aarr U8 2; aarr U8 2 ].
Definition res_A2____squeeze_avx2x4 : seq var_i :=
  [:: st_17671.(gv)
    ; buf0_17672.(gv)
    ; buf1_17673.(gv)
    ; buf2_17674.(gv)
    ; buf3_17675.(gv) ].

(* Body *)
Definition body_A2____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_17677.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17678.(gv)) AT_none (aint) (Pconst (2)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_17679.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17678) (Pvar _RATE8_17676)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_17680.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17678) (Pvar _RATE8_17676)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_17679))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_17681.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17681) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17679)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_17671.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_17671 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_17672.(gv)
                                                                  ; Lvar buf1_17673.(gv)
                                                                  ; Lvar buf2_17674.(gv)
                                                                  ; Lvar buf3_17675.(gv)
                                                                  ; Lvar offset_17677.(gv) ] A2____dumpstate_avx2x4 [:: Pvar buf0_17672
                                                                    ; Pvar buf1_17673
                                                                    ; Pvar buf2_17674
                                                                    ; Pvar buf3_17675
                                                                    ; Pvar offset_17677
                                                                    ; Pvar _RATE8_17676
                                                                    ; Pvar st_17671 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_17681.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17681) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_17680))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_17671.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_17671 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_17672.(gv)
                                                                ; Lvar buf1_17673.(gv)
                                                                ; Lvar buf2_17674.(gv)
                                                                ; Lvar buf3_17675.(gv)
                                                                ; Lvar offset_17677.(gv) ] A2____dumpstate_avx2x4 [:: Pvar buf0_17672
                                                                    ; Pvar buf1_17673
                                                                    ; Pvar buf2_17674
                                                                    ; Pvar buf3_17675
                                                                    ; Pvar offset_17677
                                                                    ; Pvar LO_17680
                                                                    ; Pvar st_17671 ]) ]
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
