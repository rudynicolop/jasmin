From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* A1184____squeeze_avx2x4 *)
(* Local variables *)
Definition st_15896 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15896).
Definition buf0_15897 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15897).
Definition buf1_15898 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15898).
Definition buf2_15899 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15899).
Definition buf3_15900 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15900).
Definition _RATE8_15901 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15901).
Definition offset_15902 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15902).
Definition _LEN_15903 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15903).
Definition ITERS_15904 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15904).
Definition LO_15905 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15905).
Definition i_15906 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15906).

(* Signature *)
Definition tyin_A1184____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aint ].
Definition args_A1184____squeeze_avx2x4 : seq var_i :=
  [:: st_15896.(gv)
    ; buf0_15897.(gv)
    ; buf1_15898.(gv)
    ; buf2_15899.(gv)
    ; buf3_15900.(gv)
    ; _RATE8_15901.(gv) ].
Definition tyout_A1184____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 1184; aarr U8 1184; aarr U8 1184; aarr U8 1184 ].
Definition res_A1184____squeeze_avx2x4 : seq var_i :=
  [:: st_15896.(gv)
    ; buf0_15897.(gv)
    ; buf1_15898.(gv)
    ; buf2_15899.(gv)
    ; buf3_15900.(gv) ].

(* Body *)
Definition body_A1184____squeeze_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_15902.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_15903.(gv)) (aint) (Pconst (1184)%Z)
    ; cassgn (Lvar ITERS_15904.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15903) (Pvar _RATE8_15901))
    ; cassgn (Lvar LO_15905.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15903) (Pvar _RATE8_15901))
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_15904))
        [:: cassgn (Lvar i_15906.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15906) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_15904)))
              [:: ccall [:: Lvar st_15896.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15896 ]
                ; ccall [:: Lvar buf0_15897.(gv)
                          ; Lvar buf1_15898.(gv)
                          ; Lvar buf2_15899.(gv)
                          ; Lvar buf3_15900.(gv)
                          ; Lvar offset_15902.(gv) ] A1184____dumpstate_avx2x4 [:: Pvar buf0_15897
                                                                    ; Pvar buf1_15898
                                                                    ; Pvar buf2_15899
                                                                    ; Pvar buf3_15900
                                                                    ; Pvar offset_15902
                                                                    ; Pvar _RATE8_15901
                                                                    ; Pvar st_15896 ]
                ; cassgn (Lvar i_15906.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15906) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ] ]
        [::]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_15905))
        [:: ccall [:: Lvar st_15896.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15896 ]
          ; ccall [:: Lvar buf0_15897.(gv)
                    ; Lvar buf1_15898.(gv)
                    ; Lvar buf2_15899.(gv)
                    ; Lvar buf3_15900.(gv)
                    ; Lvar offset_15902.(gv) ] A1184____dumpstate_avx2x4 [:: Pvar buf0_15897
                                                                    ; Pvar buf1_15898
                                                                    ; Pvar buf2_15899
                                                                    ; Pvar buf3_15900
                                                                    ; Pvar offset_15902
                                                                    ; Pvar LO_15905
                                                                    ; Pvar st_15896 ] ]
        [::] ].

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
