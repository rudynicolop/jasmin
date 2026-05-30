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

(* __m_ilen_write_upto16 *)
(* Local variables *)
Definition buf_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18894).
Definition LEN_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18895).
Definition w_4 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18896).
Definition t64 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18897).

(* Signature *)
Definition tyin___m_ilen_write_upto16 : seq atype :=
  [:: aword U64; aint; aword U128 ].
Definition args___m_ilen_write_upto16 : seq var_i :=
  [:: buf_4.(gv); LEN_4.(gv); w_4.(gv) ].
Definition tyout___m_ilen_write_upto16 : seq atype := [:: aword U64; aint ].
Definition res___m_ilen_write_upto16 : seq var_i :=
  [:: buf_4.(gv); LEN_4.(gv) ].

(* Body *)
Definition body___m_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_4))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_4))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lmem Unaligned U128 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_4))) AT_none (aword U128) (Pvar w_4))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_4.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (16)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_4.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_4) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_4))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_4)) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_4 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar buf_4.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_4.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_4) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_4
                                                                    ; Pvar w_4 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64.(gv)) AT_none (aword U64) (Pvar w_4))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_4.(gv)
                                                                  ; Lvar LEN_4.(gv) ] __m_ilen_write_upto8 [:: Pvar buf_4
                                                                    ; Pvar LEN_4
                                                                    ; Pvar t64 ]) ]) ]
                              [::]) ].

Definition fd___m_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___m_ilen_write_upto16;
    f_params := args___m_ilen_write_upto16;
    f_body := body___m_ilen_write_upto16;
    f_tyout := tyout___m_ilen_write_upto16;
    f_res := res___m_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
