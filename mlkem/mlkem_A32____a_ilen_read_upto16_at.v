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

(* A32____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_43 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17625).
Definition offset_34 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17626).
Definition DELTA_22 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17627).
Definition LEN_21 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17628).
Definition TRAIL_12 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17629).
Definition CUR_12 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17630).
Definition AT_30 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17631).
Definition w_29 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17632).
Definition AT16_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17633).
Definition t64_0_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17634).
Definition t64_1_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17635).

(* Signature *)
Definition tyin_A32____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 32; aword U64; aint; aint; aint; aint; aint ].
Definition args_A32____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_43.(gv)
    ; offset_34.(gv)
    ; DELTA_22.(gv)
    ; LEN_21.(gv)
    ; TRAIL_12.(gv)
    ; CUR_12.(gv)
    ; AT_30.(gv) ].
Definition tyout_A32____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A32____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_22.(gv); LEN_21.(gv); TRAIL_12.(gv); AT_30.(gv); w_29.(gv) ].

(* Body *)
Definition body_A32____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_30) (Pvar CUR_12)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_12) (Pconst (16)%Z)) (Pvar AT_30))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_21) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_12) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_29.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_2.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_30) (Pvar CUR_12)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_21))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_29.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_43 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_34) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_22))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_29.(gv) ] __SHLDQ [:: Pvar w_29
                                                                    ; Pvar AT16_2 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_22.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_22) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_2))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_21.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_21) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_2))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_2.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_2))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_29.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_22.(gv)
                                                                    ; Lvar LEN_21.(gv)
                                                                    ; Lvar TRAIL_12.(gv)
                                                                    ; Lvar AT16_2.(gv)
                                                                    ; Lvar t64_1_2.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_43
                                                                    ; Pvar offset_34
                                                                    ; Pvar DELTA_22
                                                                    ; Pvar LEN_21
                                                                    ; Pvar TRAIL_12
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_2 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_29.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_29
                                                                    ; Pvar t64_1_2
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_22.(gv)
                                                                    ; Lvar LEN_21.(gv)
                                                                    ; Lvar TRAIL_12.(gv)
                                                                    ; Lvar AT16_2.(gv)
                                                                    ; Lvar t64_0_2.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_43
                                                                    ; Pvar offset_34
                                                                    ; Pvar DELTA_22
                                                                    ; Pvar LEN_21
                                                                    ; Pvar TRAIL_12
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_2 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_29.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_2)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_22.(gv)
                                                                    ; Lvar LEN_21.(gv)
                                                                    ; Lvar TRAIL_12.(gv)
                                                                    ; Lvar AT16_2.(gv)
                                                                    ; Lvar t64_1_2.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_43
                                                                    ; Pvar offset_34
                                                                    ; Pvar DELTA_22
                                                                    ; Pvar LEN_21
                                                                    ; Pvar TRAIL_12
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_2 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_29.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_29
                                                                    ; Pvar t64_1_2
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_30.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_12) (Pvar AT16_2))) ]) ].

Definition fd_A32____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____a_ilen_read_upto16_at;
    f_params := args_A32____a_ilen_read_upto16_at;
    f_body := body_A32____a_ilen_read_upto16_at;
    f_tyout := tyout_A32____a_ilen_read_upto16_at;
    f_res := res_A32____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
