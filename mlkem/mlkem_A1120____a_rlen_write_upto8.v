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

(* A1120____a_rlen_write_upto8 *)
(* Local variables *)
Definition buf_131 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15344).
Definition off_25 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15345).
Definition data_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15346).
Definition len_27 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15347).
Definition zf_27 : gvar := mk_rocq_gvar Slocal (abool) (mkident 15348).

(* Signature *)
Definition tyin_A1120____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 1120; aword U64; aword U64; aword U64 ].
Definition args_A1120____a_rlen_write_upto8 : seq var_i :=
  [:: buf_131.(gv); off_25.(gv); data_8.(gv); len_27.(gv) ].
Definition tyout_A1120____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 1120; aword U64 ].
Definition res_A1120____a_rlen_write_upto8 : seq var_i :=
  [:: buf_131.(gv); off_25.(gv) ].

(* Body *)
Definition body_A1120____a_rlen_write_upto8 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_27) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf_131.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_25))) AT_none (aword U64) (Pvar data_8))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_25.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_25) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_27.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_27)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_27))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U32 buf_131.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_25))) AT_none (aword U32) (Pvar data_8))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_25.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_25) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar data_8.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar data_8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_27.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_27)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_27))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U16 buf_131.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_25))) AT_none (aword U16) (Pvar data_8))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_25.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_25) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar data_8.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar data_8) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_27.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_27)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_27))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U8 buf_131.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_25))) AT_none (aword U8) (Pvar data_8))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_25.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_25) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ]) ].

Definition fd_A1120____a_rlen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____a_rlen_write_upto8;
    f_params := args_A1120____a_rlen_write_upto8;
    f_body := body_A1120____a_rlen_write_upto8;
    f_tyout := tyout_A1120____a_rlen_write_upto8;
    f_res := res_A1120____a_rlen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
