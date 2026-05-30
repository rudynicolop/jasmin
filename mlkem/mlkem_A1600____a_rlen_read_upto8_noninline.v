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

(* A1600____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_28 : gvar := mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14973).
Definition off__8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14974).
Definition len__8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14975).
Definition w_105 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14976).
Definition off_27 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14977).
Definition len_29 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14978).
Definition zf_29 : gvar := mk_rocq_gvar Slocal (abool) (mkident 14979).
Definition sh_19 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 14980).
Definition x_28 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14981).

(* Signature *)
Definition tyin_A1600____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 1600; aword U64; aword U64 ].
Definition args_A1600____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_28.(gv); off__8.(gv); len__8.(gv) ].
Definition tyout_A1600____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A1600____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__8.(gv); w_105.(gv) ].

(* Body *)
Definition body_A1600____a_rlen_read_upto8_noninline : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar off_27.(gv)) AT_none (aword U64) (Pvar off__8))
    ; MkI dummy_instr_info (Cassgn (Lvar len_29.(gv)) AT_none (aword U64) (Pvar len__8))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_29) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_105.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_28 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_27))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_27.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_27) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_29.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_29)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_29))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_105.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_28 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_27)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_27.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_27) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_19.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_105.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_19.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_29.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_29)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_29))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_28.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_28 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_27)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_28.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_28) (Papp2 (Oland U8) (Pvar sh_19) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_105.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_105) (Pvar x_28)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_27.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_27) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_19.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_19) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_29.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_29)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_29))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_28.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_28 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_27)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_28.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_28) (Papp2 (Oland U8) (Pvar sh_19) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_105.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_105) (Pvar x_28)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_27.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_27) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ])
    ; MkI dummy_instr_info (Cassgn (Lvar off__8.(gv)) AT_none (aword U64) (Pvar off_27)) ].

Definition fd_A1600____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____a_rlen_read_upto8_noninline;
    f_params := args_A1600____a_rlen_read_upto8_noninline;
    f_body := body_A1600____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A1600____a_rlen_read_upto8_noninline;
    f_res := res_A1600____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
