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

(* A1600____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_141 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 15040).
Definition offset_149 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15041).
Definition DELTA_99 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15042).
Definition LEN_72 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15043).
Definition TRAIL_42 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15044).
Definition CUR_42 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15045).
Definition AT_98 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15046).
Definition w256_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15047).
Definition AT8_38 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15048).
Definition w_100 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15049).
Definition t128_21 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15050).

(* Signature *)
Definition tyin_A1600____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 1600; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1600____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_141.(gv)
    ; offset_149.(gv)
    ; DELTA_99.(gv)
    ; LEN_72.(gv)
    ; TRAIL_42.(gv)
    ; CUR_42.(gv)
    ; AT_98.(gv) ].
Definition tyout_A1600____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1600____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_99.(gv); LEN_72.(gv); TRAIL_42.(gv); AT_98.(gv); w256_9.(gv) ].

(* Body *)
Definition body_A1600____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_98) (Pvar CUR_42)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_42) (Pconst (8)%Z)) (Pvar AT_98))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_72) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_42) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_9.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_72))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_38.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_98) (Pvar CUR_42)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_141 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_149) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_99)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_9.(gv) ] __SHLQ_256 [:: Pvar w256_9
                                                                    ; Pvar AT8_38 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_99.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_99) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_38))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_72.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_72) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_38))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_98.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_42) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_38.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_98) (Pvar CUR_42)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_99.(gv)
                                                                  ; Lvar LEN_72.(gv)
                                                                  ; Lvar TRAIL_42.(gv)
                                                                  ; Lvar AT_98.(gv)
                                                                  ; Lvar w_100.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_141
                                                                    ; Pvar offset_149
                                                                    ; Pvar DELTA_99
                                                                    ; Pvar LEN_72
                                                                    ; Pvar TRAIL_42
                                                                    ; Pvar CUR_42
                                                                    ; Pvar AT_98 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_21.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_100)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_21 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_9.(gv) ] __SHLQ_256 [:: Pvar w256_9
                                                                    ; Pvar AT8_38 ]) ]) ]) ].

Definition fd_A1600____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____a_ilen_read_bcast_upto8_at;
    f_params := args_A1600____a_ilen_read_bcast_upto8_at;
    f_body := body_A1600____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A1600____a_ilen_read_bcast_upto8_at;
    f_res := res_A1600____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
