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

(* A33____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_61 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17170).
Definition offset_55 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17171).
Definition DELTA_37 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17172).
Definition LEN_32 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17173).
Definition w_43 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17174).
Definition t64_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17175).

(* Signature *)
Definition tyin_A33____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aword U128 ].
Definition args_A33____a_ilen_write_upto16 : seq var_i :=
  [:: buf_61.(gv); offset_55.(gv); DELTA_37.(gv); LEN_32.(gv); w_43.(gv) ].
Definition tyout_A33____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 33; aint; aint ].
Definition res_A33____a_ilen_write_upto16 : seq var_i :=
  [:: buf_61.(gv); DELTA_37.(gv); LEN_32.(gv) ].

(* Body *)
Definition body_A33____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_32))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_32))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_61.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_55) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_37))))) AT_none (aword U128) (Pvar w_43))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_37.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_37) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_32.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_32) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_32))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_61.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_55) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_37)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_43 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_37.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_37) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_32.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_32) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_43.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_43
                                                                    ; Pvar w_43 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_5.(gv)) AT_none (aword U64) (Pvar w_43))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_61.(gv)
                                                                  ; Lvar DELTA_37.(gv)
                                                                  ; Lvar LEN_32.(gv) ] A33____a_ilen_write_upto8 [:: Pvar buf_61
                                                                    ; Pvar offset_55
                                                                    ; Pvar DELTA_37
                                                                    ; Pvar LEN_32
                                                                    ; Pvar t64_5 ]) ]) ]
                              [::]) ].

Definition fd_A33____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_ilen_write_upto16;
    f_params := args_A33____a_ilen_write_upto16;
    f_body := body_A33____a_ilen_write_upto16;
    f_tyout := tyout_A33____a_ilen_write_upto16;
    f_res := res_A33____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
