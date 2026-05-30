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

(* A33____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_59 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17197).
Definition offset_53 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17198).
Definition DELTA_35 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17199).
Definition LEN_30 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17200).
Definition TRAIL_18 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17201).
Definition CUR_18 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17202).
Definition AT_42 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17203).
Definition w256_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17204).
Definition AT8_16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17205).
Definition w_41 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17206).
Definition t128_9 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17207).

(* Signature *)
Definition tyin_A33____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aint; aint; aint ].
Definition args_A33____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_59.(gv)
    ; offset_53.(gv)
    ; DELTA_35.(gv)
    ; LEN_30.(gv)
    ; TRAIL_18.(gv)
    ; CUR_18.(gv)
    ; AT_42.(gv) ].
Definition tyout_A33____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A33____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_35.(gv); LEN_30.(gv); TRAIL_18.(gv); AT_42.(gv); w256_3.(gv) ].

(* Body *)
Definition body_A33____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_42) (Pvar CUR_18)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_18) (Pconst (8)%Z)) (Pvar AT_42))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_30) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_18) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_3.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_30))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_16.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_42) (Pvar CUR_18)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_59 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_53) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_35)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_3.(gv) ] __SHLQ_256 [:: Pvar w256_3
                                                                    ; Pvar AT8_16 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_35.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_35) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_30.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_30) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_42.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_18) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_16.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_42) (Pvar CUR_18)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_35.(gv)
                                                                  ; Lvar LEN_30.(gv)
                                                                  ; Lvar TRAIL_18.(gv)
                                                                  ; Lvar AT_42.(gv)
                                                                  ; Lvar w_41.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_59
                                                                    ; Pvar offset_53
                                                                    ; Pvar DELTA_35
                                                                    ; Pvar LEN_30
                                                                    ; Pvar TRAIL_18
                                                                    ; Pvar CUR_18
                                                                    ; Pvar AT_42 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_9.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_41)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_9 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_3.(gv) ] __SHLQ_256 [:: Pvar w256_3
                                                                    ; Pvar AT8_16 ]) ]) ]) ].

Definition fd_A33____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_ilen_read_bcast_upto8_at;
    f_params := args_A33____a_ilen_read_bcast_upto8_at;
    f_body := body_A33____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A33____a_ilen_read_bcast_upto8_at;
    f_res := res_A33____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
