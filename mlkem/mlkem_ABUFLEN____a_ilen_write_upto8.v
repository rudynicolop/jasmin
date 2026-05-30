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

(* ABUFLEN____a_ilen_write_upto8 *)
(* Local variables *)
Definition buf_156 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14645).
Definition offset_167 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14646).
Definition DELTA_111 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14647).
Definition LEN_80 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14648).
Definition w_111 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14649).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aword U64 ].
Definition args_ABUFLEN____a_ilen_write_upto8 : seq var_i :=
  [:: buf_156.(gv)
    ; offset_167.(gv)
    ; DELTA_111.(gv)
    ; LEN_80.(gv)
    ; w_111.(gv) ].
Definition tyout_ABUFLEN____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 536; aint; aint ].
Definition res_ABUFLEN____a_ilen_write_upto8 : seq var_i :=
  [:: buf_156.(gv); DELTA_111.(gv); LEN_80.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_write_upto8 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_80))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_80))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U64 buf_156.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_167) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_111))))) AT_none (aword U64) (Pvar w_111))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_111.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_111) (Pconst (8)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_80.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_80) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_80))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U32 buf_156.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_167) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_111))))) AT_none (aword U32) (Pvar w_111))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_111.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar w_111) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_111.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_111) (Pconst (4)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_80.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_80) (Pconst (4)%Z))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_80))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U16 buf_156.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_167) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_111))))) AT_none (aword U16) (Pvar w_111))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_111.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar w_111) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_111.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_111) (Pconst (2)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_80.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_80) (Pconst (2)%Z))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_80))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U8 buf_156.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_167) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_111))))) AT_none (aword U8) (Pvar w_111))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_111.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_111) (Pconst (1)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_80.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_80) (Pconst (1)%Z))) ]
                                                            [::]) ]) ]
                              [::]) ].

Definition fd_ABUFLEN____a_ilen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_write_upto8;
    f_params := args_ABUFLEN____a_ilen_write_upto8;
    f_body := body_ABUFLEN____a_ilen_write_upto8;
    f_tyout := tyout_ABUFLEN____a_ilen_write_upto8;
    f_res := res_ABUFLEN____a_ilen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
