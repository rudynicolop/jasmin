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

(* A1184____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_22 : gvar := mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16119).
Definition off__5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16120).
Definition len__5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16121).
Definition w_75 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16122).
Definition off_18 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16123).
Definition len_20 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16124).
Definition zf_20 : gvar := mk_rocq_gvar Slocal (abool) (mkident 16125).
Definition sh_13 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 16126).
Definition x_22 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16127).

(* Signature *)
Definition tyin_A1184____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 1184; aword U64; aword U64 ].
Definition args_A1184____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_22.(gv); off__5.(gv); len__5.(gv) ].
Definition tyout_A1184____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A1184____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__5.(gv); w_75.(gv) ].

(* Body *)
Definition body_A1184____a_rlen_read_upto8_noninline : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar off_18.(gv)) AT_none (aword U64) (Pvar off__5))
    ; MkI dummy_instr_info (Cassgn (Lvar len_20.(gv)) AT_none (aword U64) (Pvar len__5))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_75.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_18))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_18.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_20.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_20)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_20))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_75.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_18)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_18.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_13.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_75.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_13.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_20.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_20)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_20))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_22.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_18)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_22.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_22) (Papp2 (Oland U8) (Pvar sh_13) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_75.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_75) (Pvar x_22)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_18.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_13.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_13) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_20.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_20)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_20))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_22.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_18)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_22.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_22) (Papp2 (Oland U8) (Pvar sh_13) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_75.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_75) (Pvar x_22)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_18.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ])
    ; MkI dummy_instr_info (Cassgn (Lvar off__5.(gv)) AT_none (aword U64) (Pvar off_18)) ].

Definition fd_A1184____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____a_rlen_read_upto8_noninline;
    f_params := args_A1184____a_rlen_read_upto8_noninline;
    f_body := body_A1184____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A1184____a_rlen_read_upto8_noninline;
    f_res := res_A1184____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
