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
Definition buf_15344 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15344).
Definition off_15345 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15345).
Definition data_15346 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15346).
Definition len_15347 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15347).
Definition zf_15348 : gvar := mk_rocq_gvar Slocal (abool) (mkident 15348).

(* Signature *)
Definition tyin_A1120____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 1120; aword U64; aword U64; aword U64 ].
Definition args_A1120____a_rlen_write_upto8 : seq var_i :=
  [:: buf_15344.(gv); off_15345.(gv); data_15346.(gv); len_15347.(gv) ].
Definition tyout_A1120____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 1120; aword U64 ].
Definition res_A1120____a_rlen_write_upto8 : seq var_i :=
  [:: buf_15344.(gv); off_15345.(gv) ].

(* Body *)
Definition body_A1120____a_rlen_write_upto8 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_15347) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf_15344.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15345))) AT_none (aword U64) (Pvar data_15346))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_15345.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15345) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_15348.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15347)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_15348))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U32 buf_15344.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15345))) AT_none (aword U32) (Pvar data_15346))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_15345.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15345) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar data_15346.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar data_15346) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_15348.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15347)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_15348))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U16 buf_15344.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15345))) AT_none (aword U16) (Pvar data_15346))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_15345.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15345) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar data_15346.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar data_15346) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_15348.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15347)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_15348))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U8 buf_15344.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15345))) AT_none (aword U8) (Pvar data_15346))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_15345.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15345) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
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
