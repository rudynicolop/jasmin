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

(* A1____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_10 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18276).
Definition off_ : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18277).
Definition len_ : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18278).
Definition w_16 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18279).
Definition off_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18280).
Definition len_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18281).
Definition zf_2 : gvar := mk_rocq_gvar Slocal (abool) (mkident 18282).
Definition sh_1 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 18283).
Definition x_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18284).

(* Signature *)
Definition tyin_A1____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 1; aword U64; aword U64 ].
Definition args_A1____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_10.(gv); off_.(gv); len_.(gv) ].
Definition tyout_A1____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A1____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off_.(gv); w_16.(gv) ].

(* Body *)
Definition body_A1____a_rlen_read_upto8_noninline : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar off_0.(gv)) AT_none (aword U64) (Pvar off_))
    ; MkI dummy_instr_info (Cassgn (Lvar len_2.(gv)) AT_none (aword U64) (Pvar len_))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_16.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_10 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_0))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_0.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_2)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_2))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_16.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_10 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_0)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_0.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_1.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_16.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_1.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_2)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_2))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_10.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_10 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_0)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_10.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_10) (Papp2 (Oland U8) (Pvar sh_1) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_16.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_16) (Pvar x_10)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_0.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_1.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_1) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_2)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_2))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_10.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_10 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_0)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_10.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_10) (Papp2 (Oland U8) (Pvar sh_1) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_16.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_16) (Pvar x_10)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_0.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ])
    ; MkI dummy_instr_info (Cassgn (Lvar off_.(gv)) AT_none (aword U64) (Pvar off_0)) ].

Definition fd_A1____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_rlen_read_upto8_noninline;
    f_params := args_A1____a_rlen_read_upto8_noninline;
    f_body := body_A1____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A1____a_rlen_read_upto8_noninline;
    f_res := res_A1____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
