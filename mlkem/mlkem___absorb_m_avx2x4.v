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

(* __absorb_m_avx2x4 *)
(* Local variables *)
Definition st_13 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18478).
Definition AT_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18479).
Definition buf0_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18480).
Definition buf1_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18481).
Definition buf2_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18482).
Definition buf3_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18483).
Definition _LEN_6 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18484).
Definition _TRAILB_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18485).
Definition _RATE8_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18486).
Definition ITERS_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18487).
Definition i_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18488).

(* Signature *)
Definition tyin___absorb_m_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aword U64
    ; aword U64
    ; aword U64
    ; aword U64
    ; aint
    ; aint
    ; aint ].
Definition args___absorb_m_avx2x4 : seq var_i :=
  [:: st_13.(gv)
    ; AT_8.(gv)
    ; buf0_0.(gv)
    ; buf1_0.(gv)
    ; buf2_0.(gv)
    ; buf3_0.(gv)
    ; _LEN_6.(gv)
    ; _TRAILB_4.(gv)
    ; _RATE8_2.(gv) ].
Definition tyout___absorb_m_avx2x4 : seq atype := [:: aarr U256 25; aint ].
Definition res___absorb_m_avx2x4 : seq var_i := [:: st_13.(gv); AT_8.(gv) ].

(* Body *)
Definition body___absorb_m_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_8) (Pvar _LEN_6)) (Pvar _RATE8_2))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_13.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar buf0_0.(gv)
                                                                ; Lvar buf1_0.(gv)
                                                                ; Lvar buf2_0.(gv)
                                                                ; Lvar buf3_0.(gv) ] __addstate_m_avx2x4 [:: Pvar st_13
                                                                    ; Pvar AT_8
                                                                    ; Pvar buf0_0
                                                                    ; Pvar buf1_0
                                                                    ; Pvar buf2_0
                                                                    ; Pvar buf3_0
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_2) (Pvar AT_8)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_6.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_6) (Papp2 (Osub (Op_int)) (Pvar _RATE8_2) (Pvar AT_8))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_8.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_13.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_13 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_2.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_6) (Pvar _RATE8_2)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_8.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_2)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_13.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar buf0_0.(gv)
                                                                  ; Lvar buf1_0.(gv)
                                                                  ; Lvar buf2_0.(gv)
                                                                  ; Lvar buf3_0.(gv) ] __addstate_m_avx2x4 [:: Pvar st_13
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_0
                                                                    ; Pvar buf1_0
                                                                    ; Pvar buf2_0
                                                                    ; Pvar buf3_0
                                                                    ; Pvar _RATE8_2
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_13.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_13 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_8.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_6.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_6) (Pvar _RATE8_2))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_13.(gv)
                                    ; Lvar AT_8.(gv)
                                    ; Lnone dummy_var_info (aword U64)
                                    ; Lnone dummy_var_info (aword U64)
                                    ; Lnone dummy_var_info (aword U64)
                                    ; Lnone dummy_var_info (aword U64) ] __addstate_m_avx2x4 [:: Pvar st_13
                                                                    ; Pvar AT_8
                                                                    ; Pvar buf0_0
                                                                    ; Pvar buf1_0
                                                                    ; Pvar buf2_0
                                                                    ; Pvar buf3_0
                                                                    ; Pvar _LEN_6
                                                                    ; Pvar _TRAILB_4 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_4) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_13.(gv) ] __addratebit_avx2x4 [:: Pvar st_13
                                                                    ; Pvar _RATE8_2 ]) ]
                              [::]) ].

Definition fd___absorb_m_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___absorb_m_avx2x4;
    f_params := args___absorb_m_avx2x4;
    f_body := body___absorb_m_avx2x4;
    f_tyout := tyout___absorb_m_avx2x4;
    f_res := res___absorb_m_avx2x4;
    f_extra := tt;
  |}.

End IDO.
