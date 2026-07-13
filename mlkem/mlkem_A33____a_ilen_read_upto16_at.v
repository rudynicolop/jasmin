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

(* A33____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_57 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17243).
Definition offset_51 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17244).
Definition DELTA_33 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17245).
Definition LEN_28 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17246).
Definition TRAIL_16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17247).
Definition CUR_16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17248).
Definition AT_40 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17249).
Definition w_39 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17250).
Definition AT16_3 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17251).
Definition t64_0_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17252).
Definition t64_1_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17253).

(* Signature *)
Definition tyin_A33____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aint; aint; aint ].
Definition args_A33____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_57.(gv)
    ; offset_51.(gv)
    ; DELTA_33.(gv)
    ; LEN_28.(gv)
    ; TRAIL_16.(gv)
    ; CUR_16.(gv)
    ; AT_40.(gv) ].
Definition tyout_A33____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A33____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_33.(gv); LEN_28.(gv); TRAIL_16.(gv); AT_40.(gv); w_39.(gv) ].

(* Body *)
Definition body_A33____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_40) (Pvar CUR_16)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_16) (Pconst (16)%Z)) (Pvar AT_40))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_28) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_16) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_39.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_3.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_40) (Pvar CUR_16)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_28))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_39.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_57 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_51) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_33))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_39.(gv) ] __SHLDQ [:: Pvar w_39
                                                                    ; Pvar AT16_3 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_33.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_33) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_3))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_28.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_28) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_3))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_3.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_3))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_39.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_33.(gv)
                                                                    ; Lvar LEN_28.(gv)
                                                                    ; Lvar TRAIL_16.(gv)
                                                                    ; Lvar AT16_3.(gv)
                                                                    ; Lvar t64_1_3.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_57
                                                                    ; Pvar offset_51
                                                                    ; Pvar DELTA_33
                                                                    ; Pvar LEN_28
                                                                    ; Pvar TRAIL_16
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_3 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_39.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_39
                                                                    ; Pvar t64_1_3
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_33.(gv)
                                                                    ; Lvar LEN_28.(gv)
                                                                    ; Lvar TRAIL_16.(gv)
                                                                    ; Lvar AT16_3.(gv)
                                                                    ; Lvar t64_0_3.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_57
                                                                    ; Pvar offset_51
                                                                    ; Pvar DELTA_33
                                                                    ; Pvar LEN_28
                                                                    ; Pvar TRAIL_16
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_3 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_39.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_3)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_33.(gv)
                                                                    ; Lvar LEN_28.(gv)
                                                                    ; Lvar TRAIL_16.(gv)
                                                                    ; Lvar AT16_3.(gv)
                                                                    ; Lvar t64_1_3.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_57
                                                                    ; Pvar offset_51
                                                                    ; Pvar DELTA_33
                                                                    ; Pvar LEN_28
                                                                    ; Pvar TRAIL_16
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_3 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_39.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_39
                                                                    ; Pvar t64_1_3
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_40.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_16) (Pvar AT16_3))) ]) ].

Definition fd_A33____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_ilen_read_upto16_at;
    f_params := args_A33____a_ilen_read_upto16_at;
    f_body := body_A33____a_ilen_read_upto16_at;
    f_tyout := tyout_A33____a_ilen_read_upto16_at;
    f_res := res_A33____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
