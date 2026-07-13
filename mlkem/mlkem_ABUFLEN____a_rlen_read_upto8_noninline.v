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
Definition a_30 : gvar := mk_rocq_gvar Slocal (aarr U8 536) (mkident 14591).
Definition off__9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14592).
Definition len__9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14593).
Definition w_115 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14594).
Definition off_30 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14595).
Definition len_32 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14596).
Definition zf_32 : gvar := mk_rocq_gvar Slocal (abool) (mkident 14597).
Definition sh_21 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 14598).
Definition x_30 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14599).

(* Signature *)
Definition tyin_ABUFLEN____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 536; aword U64; aword U64 ].
Definition args_ABUFLEN____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_30.(gv); off__9.(gv); len__9.(gv) ].
Definition tyout_ABUFLEN____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_ABUFLEN____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__9.(gv); w_115.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_rlen_read_upto8_noninline : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar off_30.(gv)) AT_none (aword U64) (Pvar off__9))
    ; MkI dummy_instr_info (Cassgn (Lvar len_32.(gv)) AT_none (aword U64) (Pvar len__9))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_32) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_115.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 a_30 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_30))))
                                ; MkI dummy_instr_info (Cassgn (Lvar off_30.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_30) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_32.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_32)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_32))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_115.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_30 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_30)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_30.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_30) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_21.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_115.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_21.(gv)) AT_none (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z))) ])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_32.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_32)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_32))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_30.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_30 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_30)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_30.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_30) (Papp2 (Oland U8) (Pvar sh_21) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_115.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_115) (Pvar x_30)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_30.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_30) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar sh_21.(gv)) AT_none (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_21) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lnone dummy_var_info (abool)
                                                               ; Lvar zf_32.(gv) ] AT_none (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_32)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp1 (Onot) (Pvar zf_32))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar x_30.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_30 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_30)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar x_30.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_30) (Papp2 (Oland U8) (Pvar sh_21) (Papp1 (Oword_of_int U8) (Pconst (63)%Z)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar w_115.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_115) (Pvar x_30)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar off_30.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_30) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
                                                          [::]) ])
    ; MkI dummy_instr_info (Cassgn (Lvar off__9.(gv)) AT_none (aword U64) (Pvar off_30)) ].

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
