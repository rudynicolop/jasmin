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

(* __squeeze_m_avx2 *)
(* Local variables *)
Definition st_7 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 18752).
Definition buf_11 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18753).
Definition _LEN_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18754).
Definition _RATE8_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18755).
Definition ITERS_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18756).
Definition LO : gvar := mk_rocq_gvar Slocal (aint) (mkident 18757).
Definition i_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18758).

(* Signature *)
Definition tyin___squeeze_m_avx2 : seq atype :=
  [:: aarr U256 7; aword U64; aint; aint ].
Definition args___squeeze_m_avx2 : seq var_i :=
  [:: st_7.(gv); buf_11.(gv); _LEN_2.(gv); _RATE8_0.(gv) ].
Definition tyout___squeeze_m_avx2 : seq atype := [:: aarr U256 7 ].
Definition res___squeeze_m_avx2 : seq var_i := [:: st_7.(gv) ].

(* Body *)
Definition body___squeeze_m_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar ITERS_0.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_2) (Pvar _RATE8_0)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_2) (Pvar _RATE8_0)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_3.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_0)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_7.(gv) ] _keccakf1600_avx2 [:: Pvar st_7 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_11.(gv) ] __dumpstate_m_avx2 [:: Pvar buf_11
                                                                    ; Pvar _RATE8_0
                                                                    ; Pvar st_7 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_3.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_7.(gv) ] _keccakf1600_avx2 [:: Pvar st_7 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_11.(gv) ] __dumpstate_m_avx2 [:: Pvar buf_11
                                                                    ; Pvar LO
                                                                    ; Pvar st_7 ]) ]
                              [::]) ].

Definition fd___squeeze_m_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___squeeze_m_avx2;
    f_params := args___squeeze_m_avx2;
    f_body := body___squeeze_m_avx2;
    f_tyout := tyout___squeeze_m_avx2;
    f_res := res___squeeze_m_avx2;
    f_extra := tt;
  |}.

End IDO.
