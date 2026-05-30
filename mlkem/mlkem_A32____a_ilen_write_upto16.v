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

(* A32____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_47 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17552).
Definition offset_38 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17553).
Definition DELTA_26 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17554).
Definition LEN_25 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17555).
Definition w_33 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17556).
Definition t64_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17557).

(* Signature *)
Definition tyin_A32____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 32; aword U64; aint; aint; aword U128 ].
Definition args_A32____a_ilen_write_upto16 : seq var_i :=
  [:: buf_47.(gv); offset_38.(gv); DELTA_26.(gv); LEN_25.(gv); w_33.(gv) ].
Definition tyout_A32____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 32; aint; aint ].
Definition res_A32____a_ilen_write_upto16 : seq var_i :=
  [:: buf_47.(gv); DELTA_26.(gv); LEN_25.(gv) ].

(* Body *)
Definition body_A32____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_25))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_25))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_47.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_38) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_26))))) AT_none (aword U128) (Pvar w_33))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_26.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_26) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_25.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_25) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_25))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_47.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_38) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_26)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_33 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_26.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_26) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_25.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_25) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_33.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_33
                                                                    ; Pvar w_33 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_4.(gv)) AT_none (aword U64) (Pvar w_33))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_47.(gv)
                                                                  ; Lvar DELTA_26.(gv)
                                                                  ; Lvar LEN_25.(gv) ] A32____a_ilen_write_upto8 [:: Pvar buf_47
                                                                    ; Pvar offset_38
                                                                    ; Pvar DELTA_26
                                                                    ; Pvar LEN_25
                                                                    ; Pvar t64_4 ]) ]) ]
                              [::]) ].

Definition fd_A32____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____a_ilen_write_upto16;
    f_params := args_A32____a_ilen_write_upto16;
    f_body := body_A32____a_ilen_write_upto16;
    f_tyout := tyout_A32____a_ilen_write_upto16;
    f_res := res_A32____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
