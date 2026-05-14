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
Definition buf_17197 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17197).
Definition offset_17198 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17198).
Definition DELTA_17199 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17199).
Definition LEN_17200 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17200).
Definition TRAIL_17201 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17201).
Definition CUR_17202 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17202).
Definition AT_17203 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17203).
Definition w256_17204 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17204).
Definition AT8_17205 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17205).
Definition w_17206 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17206).
Definition t128_17207 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17207).

(* Signature *)
Definition tyin_A33____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aint; aint; aint ].
Definition args_A33____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_17197.(gv)
    ; offset_17198.(gv)
    ; DELTA_17199.(gv)
    ; LEN_17200.(gv)
    ; TRAIL_17201.(gv)
    ; CUR_17202.(gv)
    ; AT_17203.(gv) ].
Definition tyout_A33____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A33____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_17199.(gv)
    ; LEN_17200.(gv)
    ; TRAIL_17201.(gv)
    ; AT_17203.(gv)
    ; w256_17204.(gv) ].

(* Body *)
Definition body_A33____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_17203) (Pvar CUR_17202)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_17202) (Pconst (8)%Z)) (Pvar AT_17203))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_17200) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_17201) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_17204.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_17200))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_17205.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17203) (Pvar CUR_17202)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_17204.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_17197 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17198) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17199)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_17204.(gv) ] __SHLQ_256 [:: Pvar w256_17204
                                                                    ; Pvar AT8_17205 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_17199.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17199) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17205))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_17200.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17200) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17205))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_17203.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_17202) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_17205.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17203) (Pvar CUR_17202)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17199.(gv)
                                                                  ; Lvar LEN_17200.(gv)
                                                                  ; Lvar TRAIL_17201.(gv)
                                                                  ; Lvar AT_17203.(gv)
                                                                  ; Lvar w_17206.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf_17197
                                                                    ; Pvar offset_17198
                                                                    ; Pvar DELTA_17199
                                                                    ; Pvar LEN_17200
                                                                    ; Pvar TRAIL_17201
                                                                    ; Pvar CUR_17202
                                                                    ; Pvar AT_17203 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_17207.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_17206)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_17204.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_17207 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_17204.(gv) ] __SHLQ_256 [:: Pvar w256_17204
                                                                    ; Pvar AT8_17205 ]) ]) ]) ].

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
