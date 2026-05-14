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

(* A33____a_rlen_write_upto8 *)
(* Local variables *)
Definition buf_17119 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17119).
Definition off_17120 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17120).
Definition data_17121 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17121).
Definition len_17122 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17122).
Definition zf_17123 : gvar := mk_rocq_gvar Slocal (abool) (mkident 17123).

(* Signature *)
Definition tyin_A33____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 33; aword U64; aword U64; aword U64 ].
Definition args_A33____a_rlen_write_upto8 : seq var_i :=
  [:: buf_17119.(gv); off_17120.(gv); data_17121.(gv); len_17122.(gv) ].
Definition tyout_A33____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 33; aword U64 ].
Definition res_A33____a_rlen_write_upto8 : seq var_i :=
  [:: buf_17119.(gv); off_17120.(gv) ].

(* Body *)
Definition body_A33____a_rlen_write_upto8 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_17122) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf_17119.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17120))) AT_none (aword U64) (Pvar data_17121))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_17120.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17120) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_17123.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17122)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_17123))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U32 buf_17119.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17120))) AT_none (aword U32) (Pvar data_17121))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_17120.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17120) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar data_17121.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar data_17121) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_17123.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17122)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_17123))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U16 buf_17119.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17120))) AT_none (aword U16) (Pvar data_17121))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_17120.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17120) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar data_17121.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar data_17121) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_17123.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17122)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_17123))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U8 buf_17119.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17120))) AT_none (aword U8) (Pvar data_17121))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_17120.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17120) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ]) ].

Definition fd_A33____a_rlen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_rlen_write_upto8;
    f_params := args_A33____a_rlen_write_upto8;
    f_body := body_A33____a_rlen_write_upto8;
    f_tyout := tyout_A33____a_rlen_write_upto8;
    f_res := res_A33____a_rlen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
