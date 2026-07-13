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

(* A1____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_19 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18316).
Definition offset_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18317).
Definition DELTA_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18318).
Definition LEN_11 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18319).
Definition w_13 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18320).
Definition t64_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18321).

(* Signature *)
Definition tyin_A1____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aword U128 ].
Definition args_A1____a_ilen_write_upto16 : seq var_i :=
  [:: buf_19.(gv); offset_4.(gv); DELTA_4.(gv); LEN_11.(gv); w_13.(gv) ].
Definition tyout_A1____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1; aint; aint ].
Definition res_A1____a_ilen_write_upto16 : seq var_i :=
  [:: buf_19.(gv); DELTA_4.(gv); LEN_11.(gv) ].

(* Body *)
Definition body_A1____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_11))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_11))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_19.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_4))))) AT_none (aword U128) (Pvar w_13))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_4.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_4) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_11.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_11) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_11))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_19.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_4)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_13 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_4.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_4) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_11.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_11) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_13.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_13
                                                                    ; Pvar w_13 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_2.(gv)) AT_none (aword U64) (Pvar w_13))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_19.(gv)
                                                                  ; Lvar DELTA_4.(gv)
                                                                  ; Lvar LEN_11.(gv) ] A1____a_ilen_write_upto8 [:: Pvar buf_19
                                                                    ; Pvar offset_4
                                                                    ; Pvar DELTA_4
                                                                    ; Pvar LEN_11
                                                                    ; Pvar t64_2 ]) ]) ]
                              [::]) ].

Definition fd_A1____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_ilen_write_upto16;
    f_params := args_A1____a_ilen_write_upto16;
    f_body := body_A1____a_ilen_write_upto16;
    f_tyout := tyout_A1____a_ilen_write_upto16;
    f_res := res_A1____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
