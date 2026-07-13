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

(* A2____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_12 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17894).
Definition off__0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17895).
Definition len__0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17896).
Definition w_26 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17897).
Definition off_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17898).
Definition len_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17899).
Definition zf_5 : gvar := mk_rocq_gvar Slocal (abool) (mkident 17900).
Definition sh_3 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 17901).
Definition x_12 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17902).

(* Signature *)
Definition tyin_A2____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 2; aword U64; aword U64 ].
Definition args_A2____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_12.(gv); off__0.(gv); len__0.(gv) ].
Definition tyout_A2____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A2____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__0.(gv); w_26.(gv) ].

(* Body *)
Definition body_A2____a_rlen_read_upto8_noninline : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar off_3.(gv)) AT_none (aword U64) (Pvar off__0))
    ; MkI dummy_instr_info (Cassgn (Lvar len_5.(gv)) AT_none (aword U64) (Pvar len__0))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_5) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_26.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_3))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_3.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_5)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_5))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_26.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_3)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_3.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_3.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_26.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_3.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_5)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_5))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_12.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_3)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_12.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_12) (Papp2 (Oland U8) (Pvar sh_3) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_26.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_26) (Pvar x_12)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_3.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_3.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_3) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_5)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_5))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_12.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_3)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_12.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_12) (Papp2 (Oland U8) (Pvar sh_3) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_26.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_26) (Pvar x_12)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_3.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ])
    ; MkI dummy_instr_info (Cassgn (Lvar off__0.(gv)) AT_none (aword U64) (Pvar off_3)) ].

Definition fd_A2____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_rlen_read_upto8_noninline;
    f_params := args_A2____a_rlen_read_upto8_noninline;
    f_body := body_A2____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A2____a_rlen_read_upto8_noninline;
    f_res := res_A2____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
