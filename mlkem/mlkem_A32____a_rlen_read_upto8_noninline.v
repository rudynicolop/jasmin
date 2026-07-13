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

(* A32____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_14 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17512).
Definition off__1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17513).
Definition len__1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17514).
Definition w_36 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17515).
Definition off_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17516).
Definition len_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17517).
Definition zf_8 : gvar := mk_rocq_gvar Slocal (abool) (mkident 17518).
Definition sh_5 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 17519).
Definition x_14 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17520).

(* Signature *)
Definition tyin_A32____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 32; aword U64; aword U64 ].
Definition args_A32____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_14.(gv); off__1.(gv); len__1.(gv) ].
Definition tyout_A32____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A32____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__1.(gv); w_36.(gv) ].

(* Body *)
Definition body_A32____a_rlen_read_upto8_noninline : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar off_6.(gv)) AT_none (aword U64) (Pvar off__1))
    ; MkI dummy_instr_info (Cassgn (Lvar len_8.(gv)) AT_none (aword U64) (Pvar len__1))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_36.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_6))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_6.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_8)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_8))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_36.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_6)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_6.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_5.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_36.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_5.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_8)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_8))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_14.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_6)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_14.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_14) (Papp2 (Oland U8) (Pvar sh_5) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_36.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_36) (Pvar x_14)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_6.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_5.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_5) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_8)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_8))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_14.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_6)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_14.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_14) (Papp2 (Oland U8) (Pvar sh_5) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_36.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_36) (Pvar x_14)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_6.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ])
    ; MkI dummy_instr_info (Cassgn (Lvar off__1.(gv)) AT_none (aword U64) (Pvar off_6)) ].

Definition fd_A32____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____a_rlen_read_upto8_noninline;
    f_params := args_A32____a_rlen_read_upto8_noninline;
    f_body := body_A32____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A32____a_rlen_read_upto8_noninline;
    f_res := res_A32____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
