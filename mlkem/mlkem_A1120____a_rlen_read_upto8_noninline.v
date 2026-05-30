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

(* A1120____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_26 : gvar := mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15355).
Definition off__7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15356).
Definition len__7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15357).
Definition w_95 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15358).
Definition off_24 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15359).
Definition len_26 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15360).
Definition zf_26 : gvar := mk_rocq_gvar Slocal (abool) (mkident 15361).
Definition sh_17 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 15362).
Definition x_26 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15363).

(* Signature *)
Definition tyin_A1120____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 1120; aword U64; aword U64 ].
Definition args_A1120____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_26.(gv); off__7.(gv); len__7.(gv) ].
Definition tyout_A1120____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A1120____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__7.(gv); w_95.(gv) ].

(* Body *)
Definition body_A1120____a_rlen_read_upto8_noninline : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar off_24.(gv)) AT_none (aword U64) (Pvar off__7))
    ; MkI dummy_instr_info (Cassgn (Lvar len_26.(gv)) AT_none (aword U64) (Pvar len__7))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_26) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_95.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_26 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_24))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_24.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_24) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_26.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_26)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_26))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_95.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_26 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_24)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_24.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_24) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_17.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_95.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_17.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_26.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_26)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_26))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_26.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_26 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_24)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_26.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_26) (Papp2 (Oland U8) (Pvar sh_17) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_95.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_95) (Pvar x_26)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_24.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_24) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_17.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_17) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_26.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_26)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_26))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_26.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_26 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_24)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_26.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_26) (Papp2 (Oland U8) (Pvar sh_17) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_95.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_95) (Pvar x_26)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_24.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_24) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ])
    ; MkI dummy_instr_info (Cassgn (Lvar off__7.(gv)) AT_none (aword U64) (Pvar off_24)) ].

Definition fd_A1120____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____a_rlen_read_upto8_noninline;
    f_params := args_A1120____a_rlen_read_upto8_noninline;
    f_body := body_A1120____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A1120____a_rlen_read_upto8_noninline;
    f_res := res_A1120____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
