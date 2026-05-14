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
Definition buf_17243 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17243).
Definition offset_17244 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17244).
Definition DELTA_17245 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17245).
Definition LEN_17246 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17246).
Definition TRAIL_17247 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17247).
Definition CUR_17248 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17248).
Definition AT_17249 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17249).
Definition w_17250 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17250).
Definition AT16_17251 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17251).
Definition t64_0_17252 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17252).
Definition t64_1_17253 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17253).

(* Signature *)
Definition tyin_A33____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aint; aint; aint ].
Definition args_A33____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_17243.(gv)
    ; offset_17244.(gv)
    ; DELTA_17245.(gv)
    ; LEN_17246.(gv)
    ; TRAIL_17247.(gv)
    ; CUR_17248.(gv)
    ; AT_17249.(gv) ].
Definition tyout_A33____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A33____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_17245.(gv)
    ; LEN_17246.(gv)
    ; TRAIL_17247.(gv)
    ; AT_17249.(gv)
    ; w_17250.(gv) ].

(* Body *)
Definition body_A33____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_17249) (Pvar CUR_17248)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_17248) (Pconst (16)%Z)) (Pvar AT_17249))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_17246) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_17247) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_17250.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_17251.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17249) (Pvar CUR_17248)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_17246))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_17250.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_17243 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17244) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17245))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_17250.(gv) ] __SHLDQ [:: Pvar w_17250
                                                                    ; Pvar AT16_17251 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_17245.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17245) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_17251))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_17246.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17246) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_17251))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_17251.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_17251))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_17250.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_17245.(gv)
                                                                    ; Lvar LEN_17246.(gv)
                                                                    ; Lvar TRAIL_17247.(gv)
                                                                    ; Lvar AT16_17251.(gv)
                                                                    ; Lvar t64_1_17253.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_17243
                                                                    ; Pvar offset_17244
                                                                    ; Pvar DELTA_17245
                                                                    ; Pvar LEN_17246
                                                                    ; Pvar TRAIL_17247
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_17251 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_17250.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_17250
                                                                    ; Pvar t64_1_17253
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_17245.(gv)
                                                                    ; Lvar LEN_17246.(gv)
                                                                    ; Lvar TRAIL_17247.(gv)
                                                                    ; Lvar AT16_17251.(gv)
                                                                    ; Lvar t64_0_17252.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_17243
                                                                    ; Pvar offset_17244
                                                                    ; Pvar DELTA_17245
                                                                    ; Pvar LEN_17246
                                                                    ; Pvar TRAIL_17247
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_17251 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_17250.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_17252)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_17245.(gv)
                                                                    ; Lvar LEN_17246.(gv)
                                                                    ; Lvar TRAIL_17247.(gv)
                                                                    ; Lvar AT16_17251.(gv)
                                                                    ; Lvar t64_1_17253.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_17243
                                                                    ; Pvar offset_17244
                                                                    ; Pvar DELTA_17245
                                                                    ; Pvar LEN_17246
                                                                    ; Pvar TRAIL_17247
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_17251 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_17250.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_17250
                                                                    ; Pvar t64_1_17253
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_17249.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_17248) (Pvar AT16_17251))) ]) ].

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
