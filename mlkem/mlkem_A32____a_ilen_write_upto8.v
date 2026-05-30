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

(* A32____a_ilen_write_upto8 *)
(* Local variables *)
Definition buf_46 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17566).
Definition offset_37 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17567).
Definition DELTA_25 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17568).
Definition LEN_24 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17569).
Definition w_32 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17570).

(* Signature *)
Definition tyin_A32____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 32; aword U64; aint; aint; aword U64 ].
Definition args_A32____a_ilen_write_upto8 : seq var_i :=
  [:: buf_46.(gv); offset_37.(gv); DELTA_25.(gv); LEN_24.(gv); w_32.(gv) ].
Definition tyout_A32____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 32; aint; aint ].
Definition res_A32____a_ilen_write_upto8 : seq var_i :=
  [:: buf_46.(gv); DELTA_25.(gv); LEN_24.(gv) ].

(* Body *)
Definition body_A32____a_ilen_write_upto8 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_24))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_24))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U64 buf_46.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_37) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_25))))) AT_none (aword U64) (Pvar w_32))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_25.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_25) (Pconst (8)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_24.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_24) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_24))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U32 buf_46.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_37) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_25))))) AT_none (aword U32) (Pvar w_32))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_32.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar w_32) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_25.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_25) (Pconst (4)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_24.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_24) (Pconst (4)%Z))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_24))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U16 buf_46.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_37) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_25))))) AT_none (aword U16) (Pvar w_32))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_32.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar w_32) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_25.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_25) (Pconst (2)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_24.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_24) (Pconst (2)%Z))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_24))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U8 buf_46.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_37) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_25))))) AT_none (aword U8) (Pvar w_32))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_25.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_25) (Pconst (1)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_24.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_24) (Pconst (1)%Z))) ]
                                                            [::]) ]) ]
                              [::]) ].

Definition fd_A32____a_ilen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____a_ilen_write_upto8;
    f_params := args_A32____a_ilen_write_upto8;
    f_body := body_A32____a_ilen_write_upto8;
    f_tyout := tyout_A32____a_ilen_write_upto8;
    f_res := res_A32____a_ilen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
