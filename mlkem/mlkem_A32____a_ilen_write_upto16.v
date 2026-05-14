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
Definition buf_17552 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17552).
Definition offset_17553 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17553).
Definition DELTA_17554 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17554).
Definition LEN_17555 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17555).
Definition w_17556 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17556).
Definition t64_17557 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17557).

(* Signature *)
Definition tyin_A32____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 32; aword U64; aint; aint; aword U128 ].
Definition args_A32____a_ilen_write_upto16 : seq var_i :=
  [:: buf_17552.(gv)
    ; offset_17553.(gv)
    ; DELTA_17554.(gv)
    ; LEN_17555.(gv)
    ; w_17556.(gv) ].
Definition tyout_A32____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 32; aint; aint ].
Definition res_A32____a_ilen_write_upto16 : seq var_i :=
  [:: buf_17552.(gv); DELTA_17554.(gv); LEN_17555.(gv) ].

(* Body *)
Definition body_A32____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_17555))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_17555))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_17552.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17553) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17554))))) AT_none (aword U128) (Pvar w_17556))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_17554.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17554) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_17555.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17555) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_17555))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_17552.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17553) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17554)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_17556 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_17554.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17554) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_17555.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17555) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_17556.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_17556
                                                                    ; Pvar w_17556 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_17557.(gv)) AT_none (aword U64) (Pvar w_17556))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_17552.(gv)
                                                                  ; Lvar DELTA_17554.(gv)
                                                                  ; Lvar LEN_17555.(gv) ] A32____a_ilen_write_upto8 [:: Pvar buf_17552
                                                                    ; Pvar offset_17553
                                                                    ; Pvar DELTA_17554
                                                                    ; Pvar LEN_17555
                                                                    ; Pvar t64_17557 ]) ]) ]
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
