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

(* A1____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_20 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18302).
Definition offset_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18303).
Definition DELTA_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18304).
Definition LEN_12 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18305).
Definition w_14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18306).
Definition t128_4 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18307).

(* Signature *)
Definition tyin_A1____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aword U256 ].
Definition args_A1____a_ilen_write_upto32 : seq var_i :=
  [:: buf_20.(gv); offset_5.(gv); DELTA_5.(gv); LEN_12.(gv); w_14.(gv) ].
Definition tyout_A1____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1; aint; aint ].
Definition res_A1____a_ilen_write_upto32 : seq var_i :=
  [:: buf_20.(gv); DELTA_5.(gv); LEN_12.(gv) ].

(* Body *)
Definition body_A1____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_12))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_12))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_20.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_5) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_5))))) AT_none (aword U256) (Pvar w_14))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_5.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_5) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_12.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_12) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_4.(gv)) AT_none (aword U128) (Pvar w_14))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_12))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_20.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_5) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_5))))) AT_none (aword U128) (Pvar t128_4))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_5.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_5) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_12.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_12) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_4.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_14
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_20.(gv)
                                                                  ; Lvar DELTA_5.(gv)
                                                                  ; Lvar LEN_12.(gv) ] A1____a_ilen_write_upto16 [:: Pvar buf_20
                                                                    ; Pvar offset_5
                                                                    ; Pvar DELTA_5
                                                                    ; Pvar LEN_12
                                                                    ; Pvar t128_4 ]) ]) ]
                              [::]) ].

Definition fd_A1____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_ilen_write_upto32;
    f_params := args_A1____a_ilen_write_upto32;
    f_body := body_A1____a_ilen_write_upto32;
    f_tyout := tyout_A1____a_ilen_write_upto32;
    f_res := res_A1____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
