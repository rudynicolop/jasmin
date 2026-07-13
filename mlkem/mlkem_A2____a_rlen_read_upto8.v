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

(* A2____a_rlen_read_upto8 *)
(* Local variables *)
Definition a_11 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17908).
Definition off_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17909).
Definition len_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17910).
Definition w_25 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17911).
Definition zf_4 : gvar := mk_rocq_gvar Slocal (abool) (mkident 17912).
Definition sh_2 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 17913).
Definition x_11 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17914).

(* Signature *)
Definition tyin_A2____a_rlen_read_upto8 : seq atype :=
  [:: aarr U8 2; aword U64; aword U64 ].
Definition args_A2____a_rlen_read_upto8 : seq var_i :=
  [:: a_11.(gv); off_2.(gv); len_4.(gv) ].
Definition tyout_A2____a_rlen_read_upto8 : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A2____a_rlen_read_upto8 : seq var_i :=
  [:: off_2.(gv); w_25.(gv) ].

(* Body *)
Definition body_A2____a_rlen_read_upto8 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_25.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_11 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_2))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_2.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_4)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_4))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_25.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_11 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_2)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_2.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_2.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_25.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_2.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_4)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_4))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_11.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_11 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_2)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_11.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_11) (Papp2 (Oland U8) (Pvar sh_2) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_25.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_25) (Pvar x_11)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_2.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_2.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_2) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_4)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_4))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_11.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_11 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_2)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_11.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_11) (Papp2 (Oland U8) (Pvar sh_2) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_25.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_25) (Pvar x_11)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_2.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ]) ].

Definition fd_A2____a_rlen_read_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_rlen_read_upto8;
    f_params := args_A2____a_rlen_read_upto8;
    f_body := body_A2____a_rlen_read_upto8;
    f_tyout := tyout_A2____a_rlen_read_upto8;
    f_res := res_A2____a_rlen_read_upto8;
    f_extra := tt;
  |}.

End IDO.
