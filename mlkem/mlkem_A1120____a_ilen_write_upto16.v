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

(* A1120____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_15395 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15395).
Definition offset_15396 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15396).
Definition DELTA_15397 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15397).
Definition LEN_15398 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15398).
Definition w_15399 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15399).
Definition t64_15400 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15400).

(* Signature *)
Definition tyin_A1120____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1120; aword U64; aint; aint; aword U128 ].
Definition args_A1120____a_ilen_write_upto16 : seq var_i :=
  [:: buf_15395.(gv)
    ; offset_15396.(gv)
    ; DELTA_15397.(gv)
    ; LEN_15398.(gv)
    ; w_15399.(gv) ].
Definition tyout_A1120____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1120; aint; aint ].
Definition res_A1120____a_ilen_write_upto16 : seq var_i :=
  [:: buf_15395.(gv); DELTA_15397.(gv); LEN_15398.(gv) ].

(* Body *)
Definition body_A1120____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_15398))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_15398))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_15395.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15396) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15397))))) AT_none (aword U128) (Pvar w_15399))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15397.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15397) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15398.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15398) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_15398))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_15395.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15396) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15397)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_15399 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_15397.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15397) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_15398.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15398) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15399.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_15399
                                                                    ; Pvar w_15399 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_15400.(gv)) AT_none (aword U64) (Pvar w_15399))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_15395.(gv)
                                                                  ; Lvar DELTA_15397.(gv)
                                                                  ; Lvar LEN_15398.(gv) ] A1120____a_ilen_write_upto8 [:: Pvar buf_15395
                                                                    ; Pvar offset_15396
                                                                    ; Pvar DELTA_15397
                                                                    ; Pvar LEN_15398
                                                                    ; Pvar t64_15400 ]) ]) ]
                              [::]) ].

Definition fd_A1120____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____a_ilen_write_upto16;
    f_params := args_A1120____a_ilen_write_upto16;
    f_body := body_A1120____a_ilen_write_upto16;
    f_tyout := tyout_A1120____a_ilen_write_upto16;
    f_res := res_A1120____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
