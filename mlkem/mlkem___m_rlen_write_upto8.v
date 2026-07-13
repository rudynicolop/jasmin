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

(* __m_rlen_write_upto8 *)
(* Local variables *)
Definition buf_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18867).
Definition data : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18868).
Definition len_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18869).
Definition zf_0 : gvar := mk_rocq_gvar Slocal (abool) (mkident 18870).

(* Signature *)
Definition tyin___m_rlen_write_upto8 : seq atype :=
  [:: aword U64; aword U64; aword U64 ].
Definition args___m_rlen_write_upto8 : seq var_i :=
  [:: buf_7.(gv); data.(gv); len_0.(gv) ].
Definition tyout___m_rlen_write_upto8 : seq atype := [:: aword U64 ].
Definition res___m_rlen_write_upto8 : seq var_i := [:: buf_7.(gv) ].

(* Body *)
Definition body___m_rlen_write_upto8 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_7))) AT_none (aword U64) (Pvar data))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf_7.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_7) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_0)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_0))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lmem Unaligned U32 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_7))) AT_none (aword U32) (Pvar data))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_7.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_7) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar data.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar data) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_0)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_0))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lmem Unaligned U16 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_7))) AT_none (aword U16) (Pvar data))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_7.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_7) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar data.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar data) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_0)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_0))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lmem Unaligned U8 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_7))) AT_none (aword U8) (Pvar data))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_7.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_7) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ]) ].

Definition fd___m_rlen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___m_rlen_write_upto8;
    f_params := args___m_rlen_write_upto8;
    f_body := body___m_rlen_write_upto8;
    f_tyout := tyout___m_rlen_write_upto8;
    f_res := res___m_rlen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
