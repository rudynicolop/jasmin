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

(* A1600____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_143 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 15013).
Definition offset_151 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15014).
Definition DELTA_101 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15015).
Definition LEN_74 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15016).
Definition w_102 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15017).
Definition t64_11 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15018).

(* Signature *)
Definition tyin_A1600____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1600; aword U64; aint; aint; aword U128 ].
Definition args_A1600____a_ilen_write_upto16 : seq var_i :=
  [:: buf_143.(gv)
    ; offset_151.(gv)
    ; DELTA_101.(gv)
    ; LEN_74.(gv)
    ; w_102.(gv) ].
Definition tyout_A1600____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1600; aint; aint ].
Definition res_A1600____a_ilen_write_upto16 : seq var_i :=
  [:: buf_143.(gv); DELTA_101.(gv); LEN_74.(gv) ].

(* Body *)
Definition body_A1600____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_74))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_74))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_143.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_151) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_101))))) AT_none (aword U128) (Pvar w_102))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_101.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_101) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_74.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_74) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_74))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_143.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_151) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_101)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_102 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_101.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_101) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_74.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_74) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_102.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_102
                                                                    ; Pvar w_102 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_11.(gv)) AT_none (aword U64) (Pvar w_102))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_143.(gv)
                                                                  ; Lvar DELTA_101.(gv)
                                                                  ; Lvar LEN_74.(gv) ] A1600____a_ilen_write_upto8 [:: Pvar buf_143
                                                                    ; Pvar offset_151
                                                                    ; Pvar DELTA_101
                                                                    ; Pvar LEN_74
                                                                    ; Pvar t64_11 ]) ]) ]
                              [::]) ].

Definition fd_A1600____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____a_ilen_write_upto16;
    f_params := args_A1600____a_ilen_write_upto16;
    f_body := body_A1600____a_ilen_write_upto16;
    f_tyout := tyout_A1600____a_ilen_write_upto16;
    f_res := res_A1600____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
