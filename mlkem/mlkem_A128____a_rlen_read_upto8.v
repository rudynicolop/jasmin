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

(* A128____a_rlen_read_upto8 *)
(* Local variables *)
Definition a_19 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16515).
Definition off_14 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16516).
Definition len_16 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16517).
Definition w_64 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16518).
Definition zf_16 : gvar := mk_rocq_gvar Slocal (abool) (mkident 16519).
Definition sh_10 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 16520).
Definition x_19 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16521).

(* Signature *)
Definition tyin_A128____a_rlen_read_upto8 : seq atype :=
  [:: aarr U8 128; aword U64; aword U64 ].
Definition args_A128____a_rlen_read_upto8 : seq var_i :=
  [:: a_19.(gv); off_14.(gv); len_16.(gv) ].
Definition tyout_A128____a_rlen_read_upto8 : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A128____a_rlen_read_upto8 : seq var_i :=
  [:: off_14.(gv); w_64.(gv) ].

(* Body *)
Definition body_A128____a_rlen_read_upto8 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_64.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_19 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_14.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_16.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_16)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_16))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_64.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_19 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_14.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_10.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_64.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_10.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_16.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_16)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_16))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_19.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_19 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_19.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_19) (Papp2 (Oland U8) (Pvar sh_10) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_64.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_64) (Pvar x_19)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_14.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_10.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_10) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_16.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_16)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_16))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_19.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_19 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_19.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_19) (Papp2 (Oland U8) (Pvar sh_10) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_64.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_64) (Pvar x_19)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_14.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ]) ].

Definition fd_A128____a_rlen_read_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____a_rlen_read_upto8;
    f_params := args_A128____a_rlen_read_upto8;
    f_body := body_A128____a_rlen_read_upto8;
    f_tyout := tyout_A128____a_rlen_read_upto8;
    f_res := res_A128____a_rlen_read_upto8;
    f_extra := tt;
  |}.

End IDO.
