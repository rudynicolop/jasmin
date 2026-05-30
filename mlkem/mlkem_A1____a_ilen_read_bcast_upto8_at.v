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

(* A1____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_17 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18343).
Definition offset_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18344).
Definition DELTA_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18345).
Definition LEN_9 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18346).
Definition TRAIL_6 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18347).
Definition CUR_6 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18348).
Definition AT_12 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18349).
Definition w256_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18350).
Definition AT8_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18351).
Definition w_11 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18352).
Definition t128_3 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18353).

(* Signature *)
Definition tyin_A1____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_17.(gv)
    ; offset_2.(gv)
    ; DELTA_2.(gv)
    ; LEN_9.(gv)
    ; TRAIL_6.(gv)
    ; CUR_6.(gv)
    ; AT_12.(gv) ].
Definition tyout_A1____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_2.(gv); LEN_9.(gv); TRAIL_6.(gv); AT_12.(gv); w256_0.(gv) ].

(* Body *)
Definition body_A1____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_12) (Pvar CUR_6)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_6) (Pconst (8)%Z)) (Pvar AT_12))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_9) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_6) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_0.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_9))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_4.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_12) (Pvar CUR_6)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_17 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_2)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_0.(gv) ] __SHLQ_256 [:: Pvar w256_0
                                                                    ; Pvar AT8_4 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_2.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_2) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_4))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_9.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_9) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_4))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_12.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_6) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_4.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_12) (Pvar CUR_6)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_2.(gv)
                                                                  ; Lvar LEN_9.(gv)
                                                                  ; Lvar TRAIL_6.(gv)
                                                                  ; Lvar AT_12.(gv)
                                                                  ; Lvar w_11.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_17
                                                                    ; Pvar offset_2
                                                                    ; Pvar DELTA_2
                                                                    ; Pvar LEN_9
                                                                    ; Pvar TRAIL_6
                                                                    ; Pvar CUR_6
                                                                    ; Pvar AT_12 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_3.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_11)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_3 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_0.(gv) ] __SHLQ_256 [:: Pvar w256_0
                                                                    ; Pvar AT8_4 ]) ]) ]) ].

Definition fd_A1____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_ilen_read_bcast_upto8_at;
    f_params := args_A1____a_ilen_read_bcast_upto8_at;
    f_body := body_A1____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A1____a_ilen_read_bcast_upto8_at;
    f_res := res_A1____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
