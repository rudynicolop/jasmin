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

(* A1568____a_ilen_write_upto8 *)
(* Local variables *)
Definition buf_114 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15791).
Definition offset_116 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15792).
Definition DELTA_78 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15793).
Definition LEN_59 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15794).
Definition w_81 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15795).

(* Signature *)
Definition tyin_A1568____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aword U64 ].
Definition args_A1568____a_ilen_write_upto8 : seq var_i :=
  [:: buf_114.(gv); offset_116.(gv); DELTA_78.(gv); LEN_59.(gv); w_81.(gv) ].
Definition tyout_A1568____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 1568; aint; aint ].
Definition res_A1568____a_ilen_write_upto8 : seq var_i :=
  [:: buf_114.(gv); DELTA_78.(gv); LEN_59.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_write_upto8 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_59))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_59))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U64 buf_114.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_116) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_78))))) AT_none (aword U64) (Pvar w_81))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_78.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_78) (Pconst (8)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_59.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_59) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_59))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U32 buf_114.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_116) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_78))))) AT_none (aword U32) (Pvar w_81))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_81.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar w_81) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_78.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_78) (Pconst (4)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_59.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_59) (Pconst (4)%Z))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_59))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U16 buf_114.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_116) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_78))))) AT_none (aword U16) (Pvar w_81))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_81.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar w_81) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_78.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_78) (Pconst (2)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_59.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_59) (Pconst (2)%Z))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_59))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U8 buf_114.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_116) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_78))))) AT_none (aword U8) (Pvar w_81))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_78.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_78) (Pconst (1)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_59.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_59) (Pconst (1)%Z))) ]
                                                            [::]) ]) ]
                              [::]) ].

Definition fd_A1568____a_ilen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_ilen_write_upto8;
    f_params := args_A1568____a_ilen_write_upto8;
    f_body := body_A1568____a_ilen_write_upto8;
    f_tyout := tyout_A1568____a_ilen_write_upto8;
    f_res := res_A1568____a_ilen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
