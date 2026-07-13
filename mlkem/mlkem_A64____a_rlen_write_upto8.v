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

(* A64____a_rlen_write_upto8 *)
(* Local variables *)
Definition buf_77 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16737).
Definition off_13 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16738).
Definition data_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16739).
Definition len_15 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16740).
Definition zf_15 : gvar := mk_rocq_gvar Slocal (abool) (mkident 16741).

(* Signature *)
Definition tyin_A64____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 64; aword U64; aword U64; aword U64 ].
Definition args_A64____a_rlen_write_upto8 : seq var_i :=
  [:: buf_77.(gv); off_13.(gv); data_4.(gv); len_15.(gv) ].
Definition tyout_A64____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 64; aword U64 ].
Definition res_A64____a_rlen_write_upto8 : seq var_i :=
  [:: buf_77.(gv); off_13.(gv) ].

(* Body *)
Definition body_A64____a_rlen_write_upto8 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_15) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf_77.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_13))) AT_none (aword U64) (Pvar data_4))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_13.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_13) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_15.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_15))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U32 buf_77.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_13))) AT_none (aword U32) (Pvar data_4))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_13.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_13) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar data_4.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar data_4) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_15.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_15))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U16 buf_77.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_13))) AT_none (aword U16) (Pvar data_4))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_13.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_13) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar data_4.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar data_4) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_15.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_15))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U8 buf_77.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_13))) AT_none (aword U8) (Pvar data_4))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_13.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_13) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ]) ].

Definition fd_A64____a_rlen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_rlen_write_upto8;
    f_params := args_A64____a_rlen_write_upto8;
    f_body := body_A64____a_rlen_write_upto8;
    f_tyout := tyout_A64____a_rlen_write_upto8;
    f_res := res_A64____a_rlen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
