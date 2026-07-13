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

(* A1568____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_113 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15804).
Definition offset_115 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15805).
Definition DELTA_77 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15806).
Definition LEN_58 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15807).
Definition TRAIL_34 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15808).
Definition CUR_34 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15809).
Definition AT_78 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15810).
Definition w256_7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15811).
Definition AT8_30 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15812).
Definition w_80 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15813).
Definition t128_17 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15814).

(* Signature *)
Definition tyin_A1568____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1568____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_113.(gv)
    ; offset_115.(gv)
    ; DELTA_77.(gv)
    ; LEN_58.(gv)
    ; TRAIL_34.(gv)
    ; CUR_34.(gv)
    ; AT_78.(gv) ].
Definition tyout_A1568____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1568____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_77.(gv); LEN_58.(gv); TRAIL_34.(gv); AT_78.(gv); w256_7.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_78) (Pvar CUR_34)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_34) (Pconst (8)%Z)) (Pvar AT_78))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_58) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_34) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_7.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_58))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_30.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_78) (Pvar CUR_34)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_113 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_115) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_77)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_7.(gv) ] __SHLQ_256 [:: Pvar w256_7
                                                                    ; Pvar AT8_30 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_77.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_77) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_30))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_58.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_58) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_30))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_78.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_34) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_30.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_78) (Pvar CUR_34)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_77.(gv)
                                                                  ; Lvar LEN_58.(gv)
                                                                  ; Lvar TRAIL_34.(gv)
                                                                  ; Lvar AT_78.(gv)
                                                                  ; Lvar w_80.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_113
                                                                    ; Pvar offset_115
                                                                    ; Pvar DELTA_77
                                                                    ; Pvar LEN_58
                                                                    ; Pvar TRAIL_34
                                                                    ; Pvar CUR_34
                                                                    ; Pvar AT_78 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_17.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_80)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_17 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_7.(gv) ] __SHLQ_256 [:: Pvar w256_7
                                                                    ; Pvar AT8_30 ]) ]) ]) ].

Definition fd_A1568____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_ilen_read_bcast_upto8_at;
    f_params := args_A1568____a_ilen_read_bcast_upto8_at;
    f_body := body_A1568____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A1568____a_ilen_read_bcast_upto8_at;
    f_res := res_A1568____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
