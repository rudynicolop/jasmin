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

(* A1184____squeeze_avx2x4 *)
(* Local variables *)
Definition st_79 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15896).
Definition buf0_26 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15897).
Definition buf1_26 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15898).
Definition buf2_26 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15899).
Definition buf3_26 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15900).
Definition _RATE8_35 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15901).
Definition offset_111 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15902).
Definition _LEN_72 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15903).
Definition ITERS_35 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15904).
Definition LO_13 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15905).
Definition i_48 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15906).

(* Signature *)
Definition tyin_A1184____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aint ].
Definition args_A1184____squeeze_avx2x4 : seq var_i :=
  [:: st_79.(gv)
    ; buf0_26.(gv)
    ; buf1_26.(gv)
    ; buf2_26.(gv)
    ; buf3_26.(gv)
    ; _RATE8_35.(gv) ].
Definition tyout_A1184____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 1184; aarr U8 1184; aarr U8 1184; aarr U8 1184 ].
Definition res_A1184____squeeze_avx2x4 : seq var_i :=
  [:: st_79.(gv); buf0_26.(gv); buf1_26.(gv); buf2_26.(gv); buf3_26.(gv) ].

(* Body *)
Definition body_A1184____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_111.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_72.(gv)) AT_none (aint) (Pconst (1184)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_35.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_72) (Pvar _RATE8_35)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_13.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_72) (Pvar _RATE8_35)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_35))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_48.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_48) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_35)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_79.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_79 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_26.(gv)
                                                                  ; Lvar buf1_26.(gv)
                                                                  ; Lvar buf2_26.(gv)
                                                                  ; Lvar buf3_26.(gv)
                                                                  ; Lvar offset_111.(gv) ] A1184____dumpstate_avx2x4 [:: Pvar buf0_26
                                                                    ; Pvar buf1_26
                                                                    ; Pvar buf2_26
                                                                    ; Pvar buf3_26
                                                                    ; Pvar offset_111
                                                                    ; Pvar _RATE8_35
                                                                    ; Pvar st_79 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_48.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_48) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_13))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_79.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_79 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_26.(gv)
                                                                ; Lvar buf1_26.(gv)
                                                                ; Lvar buf2_26.(gv)
                                                                ; Lvar buf3_26.(gv)
                                                                ; Lvar offset_111.(gv) ] A1184____dumpstate_avx2x4 [:: Pvar buf0_26
                                                                    ; Pvar buf1_26
                                                                    ; Pvar buf2_26
                                                                    ; Pvar buf3_26
                                                                    ; Pvar offset_111
                                                                    ; Pvar LO_13
                                                                    ; Pvar st_79 ]) ]
                              [::]) ].

Definition fd_A1184____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____squeeze_avx2x4;
    f_params := args_A1184____squeeze_avx2x4;
    f_body := body_A1184____squeeze_avx2x4;
    f_tyout := tyout_A1184____squeeze_avx2x4;
    f_res := res_A1184____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
