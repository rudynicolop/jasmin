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

(* A33____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_16 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17130).
Definition off__2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17131).
Definition len__2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17132).
Definition w_46 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17133).
Definition off_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17134).
Definition len_11 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17135).
Definition zf_11 : gvar := mk_rocq_gvar Slocal (abool) (mkident 17136).
Definition sh_7 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 17137).
Definition x_16 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17138).

(* Signature *)
Definition tyin_A33____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 33; aword U64; aword U64 ].
Definition args_A33____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_16.(gv); off__2.(gv); len__2.(gv) ].
Definition tyout_A33____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A33____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__2.(gv); w_46.(gv) ].

(* Body *)
Definition body_A33____a_rlen_read_upto8_noninline : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar off_9.(gv)) AT_none (aword U64) (Pvar off__2))
    ; MkI dummy_instr_info (Cassgn (Lvar len_11.(gv)) AT_none (aword U64) (Pvar len__2))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_11) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_46.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_16 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_9))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_9.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_9) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_11)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_11))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_46.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_16 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_9)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_9.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_9) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_7.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_46.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_7.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_11)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_11))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_16.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_16 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_9)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_16.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_16) (Papp2 (Oland U8) (Pvar sh_7) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_46.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_46) (Pvar x_16)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_9.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_9) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_7.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_7) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_11.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_11)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_11))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_16.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_16 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_9)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_16.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_16) (Papp2 (Oland U8) (Pvar sh_7) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_46.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_46) (Pvar x_16)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_9.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_9) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ])
    ; MkI dummy_instr_info (Cassgn (Lvar off__2.(gv)) AT_none (aword U64) (Pvar off_9)) ].

Definition fd_A33____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_rlen_read_upto8_noninline;
    f_params := args_A33____a_rlen_read_upto8_noninline;
    f_body := body_A33____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A33____a_rlen_read_upto8_noninline;
    f_res := res_A33____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
