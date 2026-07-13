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

(* __squeeze_m_avx2x4 *)
(* Local variables *)
Definition st_15 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18435).
Definition buf0_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18436).
Definition buf1_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18437).
Definition buf2_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18438).
Definition buf3_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18439).
Definition _LEN_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18440).
Definition _RATE8_3 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18441).
Definition ITERS_3 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18442).
Definition LO_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18443).
Definition i_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18444).

(* Signature *)
Definition tyin___squeeze_m_avx2x4 : seq atype :=
  [:: aarr U256 25; aword U64; aword U64; aword U64; aword U64; aint; aint ].
Definition args___squeeze_m_avx2x4 : seq var_i :=
  [:: st_15.(gv)
    ; buf0_2.(gv)
    ; buf1_2.(gv)
    ; buf2_2.(gv)
    ; buf3_2.(gv)
    ; _LEN_8.(gv)
    ; _RATE8_3.(gv) ].
Definition tyout___squeeze_m_avx2x4 : seq atype := [:: aarr U256 25 ].
Definition res___squeeze_m_avx2x4 : seq var_i := [:: st_15.(gv) ].

(* Body *)
Definition body___squeeze_m_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar ITERS_3.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_8) (Pvar _RATE8_3)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_0.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_8) (Pvar _RATE8_3)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_3))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_10.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_3)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_15.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_2.(gv)
                                                                  ; Lvar buf1_2.(gv)
                                                                  ; Lvar buf2_2.(gv)
                                                                  ; Lvar buf3_2.(gv) ] __dumpstate_m_avx2x4 [:: Pvar buf0_2
                                                                    ; Pvar buf1_2
                                                                    ; Pvar buf2_2
                                                                    ; Pvar buf3_2
                                                                    ; Pvar _RATE8_3
                                                                    ; Pvar st_15 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_10.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_0))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_15.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_2.(gv)
                                                                ; Lvar buf1_2.(gv)
                                                                ; Lvar buf2_2.(gv)
                                                                ; Lvar buf3_2.(gv) ] __dumpstate_m_avx2x4 [:: Pvar buf0_2
                                                                    ; Pvar buf1_2
                                                                    ; Pvar buf2_2
                                                                    ; Pvar buf3_2
                                                                    ; Pvar LO_0
                                                                    ; Pvar st_15 ]) ]
                              [::]) ].

Definition fd___squeeze_m_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___squeeze_m_avx2x4;
    f_params := args___squeeze_m_avx2x4;
    f_body := body___squeeze_m_avx2x4;
    f_tyout := tyout___squeeze_m_avx2x4;
    f_res := res___squeeze_m_avx2x4;
    f_extra := tt;
  |}.

End IDO.
