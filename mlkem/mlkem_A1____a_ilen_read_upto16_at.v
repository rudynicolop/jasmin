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

(* A1____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_15 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18389).
Definition offset_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18390).
Definition DELTA_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18391).
Definition LEN_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18392).
Definition TRAIL_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18393).
Definition CUR_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18394).
Definition AT_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18395).
Definition w_9 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18396).
Definition AT16_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18397).
Definition t64_0_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18398).
Definition t64_1_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18399).

(* Signature *)
Definition tyin_A1____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_15.(gv)
    ; offset_0.(gv)
    ; DELTA_0.(gv)
    ; LEN_7.(gv)
    ; TRAIL_4.(gv)
    ; CUR_4.(gv)
    ; AT_10.(gv) ].
Definition tyout_A1____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A1____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_0.(gv); LEN_7.(gv); TRAIL_4.(gv); AT_10.(gv); w_9.(gv) ].

(* Body *)
Definition body_A1____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_10) (Pvar CUR_4)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_4) (Pconst (16)%Z)) (Pvar AT_10))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_7) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_4) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_9.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_0.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_10) (Pvar CUR_4)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_7))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_9.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_15 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_0))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_9.(gv) ] __SHLDQ [:: Pvar w_9
                                                                    ; Pvar AT16_0 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_0.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_0) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_0))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_7.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_7) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_0))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_0.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_0))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_9.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_0.(gv)
                                                                    ; Lvar LEN_7.(gv)
                                                                    ; Lvar TRAIL_4.(gv)
                                                                    ; Lvar AT16_0.(gv)
                                                                    ; Lvar t64_1_0.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_15
                                                                    ; Pvar offset_0
                                                                    ; Pvar DELTA_0
                                                                    ; Pvar LEN_7
                                                                    ; Pvar TRAIL_4
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_0 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_9
                                                                    ; Pvar t64_1_0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_0.(gv)
                                                                    ; Lvar LEN_7.(gv)
                                                                    ; Lvar TRAIL_4.(gv)
                                                                    ; Lvar AT16_0.(gv)
                                                                    ; Lvar t64_0_0.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_15
                                                                    ; Pvar offset_0
                                                                    ; Pvar DELTA_0
                                                                    ; Pvar LEN_7
                                                                    ; Pvar TRAIL_4
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_0 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_9.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_0)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_0.(gv)
                                                                    ; Lvar LEN_7.(gv)
                                                                    ; Lvar TRAIL_4.(gv)
                                                                    ; Lvar AT16_0.(gv)
                                                                    ; Lvar t64_1_0.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_15
                                                                    ; Pvar offset_0
                                                                    ; Pvar DELTA_0
                                                                    ; Pvar LEN_7
                                                                    ; Pvar TRAIL_4
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_0 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_9
                                                                    ; Pvar t64_1_0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_10.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_4) (Pvar AT16_0))) ]) ].

Definition fd_A1____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_ilen_read_upto16_at;
    f_params := args_A1____a_ilen_read_upto16_at;
    f_body := body_A1____a_ilen_read_upto16_at;
    f_tyout := tyout_A1____a_ilen_read_upto16_at;
    f_res := res_A1____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
