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

(* A2____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_29 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 18007).
Definition offset_17 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18008).
Definition DELTA_11 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18009).
Definition LEN_14 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18010).
Definition TRAIL_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18011).
Definition CUR_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18012).
Definition AT_20 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18013).
Definition w_19 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18014).
Definition AT16_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18015).
Definition t64_0_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18016).
Definition t64_1_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18017).

(* Signature *)
Definition tyin_A2____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aint; aint; aint ].
Definition args_A2____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_29.(gv)
    ; offset_17.(gv)
    ; DELTA_11.(gv)
    ; LEN_14.(gv)
    ; TRAIL_8.(gv)
    ; CUR_8.(gv)
    ; AT_20.(gv) ].
Definition tyout_A2____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A2____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_11.(gv); LEN_14.(gv); TRAIL_8.(gv); AT_20.(gv); w_19.(gv) ].

(* Body *)
Definition body_A2____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_20) (Pvar CUR_8)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_8) (Pconst (16)%Z)) (Pvar AT_20))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_14) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_8) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_19.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_1.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_20) (Pvar CUR_8)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_14))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_19.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_29 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_11))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_19.(gv) ] __SHLDQ [:: Pvar w_19
                                                                    ; Pvar AT16_1 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_11.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_11) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_1))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_14.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_1))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_1.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_1))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_19.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_11.(gv)
                                                                    ; Lvar LEN_14.(gv)
                                                                    ; Lvar TRAIL_8.(gv)
                                                                    ; Lvar AT16_1.(gv)
                                                                    ; Lvar t64_1_1.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_29
                                                                    ; Pvar offset_17
                                                                    ; Pvar DELTA_11
                                                                    ; Pvar LEN_14
                                                                    ; Pvar TRAIL_8
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_1 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_19.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_19
                                                                    ; Pvar t64_1_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_11.(gv)
                                                                    ; Lvar LEN_14.(gv)
                                                                    ; Lvar TRAIL_8.(gv)
                                                                    ; Lvar AT16_1.(gv)
                                                                    ; Lvar t64_0_1.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_29
                                                                    ; Pvar offset_17
                                                                    ; Pvar DELTA_11
                                                                    ; Pvar LEN_14
                                                                    ; Pvar TRAIL_8
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_1 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_19.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_1)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_11.(gv)
                                                                    ; Lvar LEN_14.(gv)
                                                                    ; Lvar TRAIL_8.(gv)
                                                                    ; Lvar AT16_1.(gv)
                                                                    ; Lvar t64_1_1.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_29
                                                                    ; Pvar offset_17
                                                                    ; Pvar DELTA_11
                                                                    ; Pvar LEN_14
                                                                    ; Pvar TRAIL_8
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_1 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_19.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_19
                                                                    ; Pvar t64_1_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_20.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_8) (Pvar AT16_1))) ]) ].

Definition fd_A2____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_ilen_read_upto16_at;
    f_params := args_A2____a_ilen_read_upto16_at;
    f_body := body_A2____a_ilen_read_upto16_at;
    f_tyout := tyout_A2____a_ilen_read_upto16_at;
    f_res := res_A2____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
