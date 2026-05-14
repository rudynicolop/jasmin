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

(* A1120____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_15468 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15468).
Definition offset_15469 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15469).
Definition DELTA_15470 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15470).
Definition LEN_15471 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15471).
Definition TRAIL_15472 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15472).
Definition CUR_15473 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15473).
Definition AT_15474 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15474).
Definition w_15475 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15475).
Definition AT16_15476 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15476).
Definition t64_0_15477 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15477).
Definition t64_1_15478 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15478).

(* Signature *)
Definition tyin_A1120____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 1120; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1120____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_15468.(gv)
    ; offset_15469.(gv)
    ; DELTA_15470.(gv)
    ; LEN_15471.(gv)
    ; TRAIL_15472.(gv)
    ; CUR_15473.(gv)
    ; AT_15474.(gv) ].
Definition tyout_A1120____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A1120____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_15470.(gv)
    ; LEN_15471.(gv)
    ; TRAIL_15472.(gv)
    ; AT_15474.(gv)
    ; w_15475.(gv) ].

(* Body *)
Definition body_A1120____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15474) (Pvar CUR_15473)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15473) (Pconst (16)%Z)) (Pvar AT_15474))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15471) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15472) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_15475.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_15476.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15474) (Pvar CUR_15473)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_15471))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_15475.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_15468 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15469) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15470))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_15475.(gv) ] __SHLDQ [:: Pvar w_15475
                                                                    ; Pvar AT16_15476 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15470.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15470) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_15476))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15471.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15471) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_15476))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_15476.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_15476))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15475.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15470.(gv)
                                                                    ; Lvar LEN_15471.(gv)
                                                                    ; Lvar TRAIL_15472.(gv)
                                                                    ; Lvar AT16_15476.(gv)
                                                                    ; Lvar t64_1_15478.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_15468
                                                                    ; Pvar offset_15469
                                                                    ; Pvar DELTA_15470
                                                                    ; Pvar LEN_15471
                                                                    ; Pvar TRAIL_15472
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_15476 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15475.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_15475
                                                                    ; Pvar t64_1_15478
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15470.(gv)
                                                                    ; Lvar LEN_15471.(gv)
                                                                    ; Lvar TRAIL_15472.(gv)
                                                                    ; Lvar AT16_15476.(gv)
                                                                    ; Lvar t64_0_15477.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_15468
                                                                    ; Pvar offset_15469
                                                                    ; Pvar DELTA_15470
                                                                    ; Pvar LEN_15471
                                                                    ; Pvar TRAIL_15472
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_15476 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_15475.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_15477)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15470.(gv)
                                                                    ; Lvar LEN_15471.(gv)
                                                                    ; Lvar TRAIL_15472.(gv)
                                                                    ; Lvar AT16_15476.(gv)
                                                                    ; Lvar t64_1_15478.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_15468
                                                                    ; Pvar offset_15469
                                                                    ; Pvar DELTA_15470
                                                                    ; Pvar LEN_15471
                                                                    ; Pvar TRAIL_15472
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_15476 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15475.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_15475
                                                                    ; Pvar t64_1_15478
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15474.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15473) (Pvar AT16_15476))) ]) ].

Definition fd_A1120____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____a_ilen_read_upto16_at;
    f_params := args_A1120____a_ilen_read_upto16_at;
    f_body := body_A1120____a_ilen_read_upto16_at;
    f_tyout := tyout_A1120____a_ilen_read_upto16_at;
    f_res := res_A1120____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
