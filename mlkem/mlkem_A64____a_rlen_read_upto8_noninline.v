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

(* A64____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_18 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16748).
Definition off__3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16749).
Definition len__3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16750).
Definition w_56 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16751).
Definition off_12 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16752).
Definition len_14 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16753).
Definition zf_14 : gvar := mk_rocq_gvar Slocal (abool) (mkident 16754).
Definition sh_9 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 16755).
Definition x_18 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16756).

(* Signature *)
Definition tyin_A64____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 64; aword U64; aword U64 ].
Definition args_A64____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_18.(gv); off__3.(gv); len__3.(gv) ].
Definition tyout_A64____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A64____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__3.(gv); w_56.(gv) ].

(* Body *)
Definition body_A64____a_rlen_read_upto8_noninline : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar off_12.(gv)) AT_none (aword U64) (Pvar off__3))
    ; MkI dummy_instr_info (Cassgn (Lvar len_14.(gv)) AT_none (aword U64) (Pvar len__3))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_14) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_56.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_18 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_12))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_12.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_14))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_56.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_18 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_12)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_12.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_9.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_56.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_9.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_14))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_18.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_18 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_12)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_18.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_18) (Papp2 (Oland U8) (Pvar sh_9) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_56.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_56) (Pvar x_18)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_12.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_9.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_9) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_14))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_18.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_18 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_12)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_18.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_18) (Papp2 (Oland U8) (Pvar sh_9) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_56.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_56) (Pvar x_18)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_12.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ])
    ; MkI dummy_instr_info (Cassgn (Lvar off__3.(gv)) AT_none (aword U64) (Pvar off_12)) ].

Definition fd_A64____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_rlen_read_upto8_noninline;
    f_params := args_A64____a_rlen_read_upto8_noninline;
    f_body := body_A64____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A64____a_rlen_read_upto8_noninline;
    f_res := res_A64____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
