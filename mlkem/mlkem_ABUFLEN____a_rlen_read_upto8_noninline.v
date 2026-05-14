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

(* ABUFLEN____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_14591 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14591).
Definition off__14592 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14592).
Definition len__14593 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14593).
Definition w_14594 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14594).
Definition off_14595 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14595).
Definition len_14596 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14596).
Definition zf_14597 : gvar := mk_rocq_gvar Slocal (abool) (mkident 14597).
Definition sh_14598 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 14598).
Definition x_14599 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14599).

(* Signature *)
Definition tyin_ABUFLEN____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 536; aword U64; aword U64 ].
Definition args_ABUFLEN____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_14591.(gv); off__14592.(gv); len__14593.(gv) ].
Definition tyout_ABUFLEN____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_ABUFLEN____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__14592.(gv); w_14594.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_rlen_read_upto8_noninline : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar off_14595.(gv)) AT_none (aword U64) (Pvar off__14592))
    ; MkI dummy_instr_info (Cassgn (Lvar len_14596.(gv)) AT_none (aword U64) (Pvar len__14593))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_14596) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_14594.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_14591 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14595))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_14595.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14595) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_14597.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14596)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_14597))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_14594.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_14591 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14595)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_14595.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14595) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_14598.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_14594.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_14598.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_14597.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14596)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_14597))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_14599.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_14591 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14595)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_14599.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_14599) (Papp2 (Oland U8) (Pvar sh_14598) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_14594.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_14594) (Pvar x_14599)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_14595.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14595) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_14598.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_14598) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_14597.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14596)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_14597))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_14599.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_14591 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14595)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_14599.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_14599) (Papp2 (Oland U8) (Pvar sh_14598) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_14594.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_14594) (Pvar x_14599)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_14595.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14595) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ])
    ; MkI dummy_instr_info (Cassgn (Lvar off__14592.(gv)) AT_none (aword U64) (Pvar off_14595)) ].

Definition fd_ABUFLEN____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_rlen_read_upto8_noninline;
    f_params := args_ABUFLEN____a_rlen_read_upto8_noninline;
    f_body := body_ABUFLEN____a_rlen_read_upto8_noninline;
    f_tyout := tyout_ABUFLEN____a_rlen_read_upto8_noninline;
    f_res := res_ABUFLEN____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
