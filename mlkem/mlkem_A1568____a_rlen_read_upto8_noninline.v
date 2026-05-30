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

(* A1568____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_24 : gvar := mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15737).
Definition off__6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15738).
Definition len__6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15739).
Definition w_85 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15740).
Definition off_21 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15741).
Definition len_23 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15742).
Definition zf_23 : gvar := mk_rocq_gvar Slocal (abool) (mkident 15743).
Definition sh_15 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 15744).
Definition x_24 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15745).

(* Signature *)
Definition tyin_A1568____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 1568; aword U64; aword U64 ].
Definition args_A1568____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_24.(gv); off__6.(gv); len__6.(gv) ].
Definition tyout_A1568____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A1568____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__6.(gv); w_85.(gv) ].

(* Body *)
Definition body_A1568____a_rlen_read_upto8_noninline : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar off_21.(gv)) AT_none (aword U64) (Pvar off__6))
    ; MkI dummy_instr_info (Cassgn (Lvar len_23.(gv)) AT_none (aword U64) (Pvar len__6))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_23) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_85.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_21))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_21.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_21) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_23.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_23)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_23))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_85.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_21)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_21.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_21) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_15.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_85.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_15.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_23.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_23)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_23))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_24.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_21)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_24.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_24) (Papp2 (Oland U8) (Pvar sh_15) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_85.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_85) (Pvar x_24)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_21.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_21) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_15.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_15) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_23.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_23)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_23))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_24.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_21)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_24.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_24) (Papp2 (Oland U8) (Pvar sh_15) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_85.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_85) (Pvar x_24)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_21.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_21) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ])
    ; MkI dummy_instr_info (Cassgn (Lvar off__6.(gv)) AT_none (aword U64) (Pvar off_21)) ].

Definition fd_A1568____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_rlen_read_upto8_noninline;
    f_params := args_A1568____a_rlen_read_upto8_noninline;
    f_body := body_A1568____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A1568____a_rlen_read_upto8_noninline;
    f_res := res_A1568____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
