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

(* __m_ilen_write_upto8 *)
(* Local variables *)
Definition buf_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18903).
Definition LEN_3 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18904).
Definition w_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18905).

(* Signature *)
Definition tyin___m_ilen_write_upto8 : seq atype :=
  [:: aword U64; aint; aword U64 ].
Definition args___m_ilen_write_upto8 : seq var_i :=
  [:: buf_3.(gv); LEN_3.(gv); w_3.(gv) ].
Definition tyout___m_ilen_write_upto8 : seq atype := [:: aword U64; aint ].
Definition res___m_ilen_write_upto8 : seq var_i :=
  [:: buf_3.(gv); LEN_3.(gv) ].

(* Body *)
Definition body___m_ilen_write_upto8 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_3))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_3))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_3))) AT_none (aword U64) (Pvar w_3))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_3.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_3.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_3) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_3))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lmem Unaligned U32 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_3))) AT_none (aword U32) (Pvar w_3))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_3.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar w_3) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar buf_3.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_3.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_3) (Pconst (4)%Z))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_3))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lmem Unaligned U16 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_3))) AT_none (aword U16) (Pvar w_3))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_3.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar w_3) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar buf_3.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_3.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_3) (Pconst (2)%Z))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_3))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lmem Unaligned U8 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_3))) AT_none (aword U8) (Pvar w_3))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar buf_3.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_3.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_3) (Pconst (1)%Z))) ]
                                                            [::]) ]) ]
                              [::]) ].

Definition fd___m_ilen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___m_ilen_write_upto8;
    f_params := args___m_ilen_write_upto8;
    f_body := body___m_ilen_write_upto8;
    f_tyout := tyout___m_ilen_write_upto8;
    f_res := res___m_ilen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
