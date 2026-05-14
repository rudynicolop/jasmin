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
Definition buf_15040 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 15040).
Definition offset_15041 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15041).
Definition DELTA_15042 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15042).
Definition LEN_15043 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15043).
Definition TRAIL_15044 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15044).
Definition CUR_15045 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15045).
Definition AT_15046 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15046).
Definition w256_15047 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15047).
Definition AT8_15048 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15048).
Definition w_15049 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15049).
Definition t128_15050 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15050).

(* Signature *)
Definition tyin_A1600____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 1600; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1600____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_15040.(gv)
    ; offset_15041.(gv)
    ; DELTA_15042.(gv)
    ; LEN_15043.(gv)
    ; TRAIL_15044.(gv)
    ; CUR_15045.(gv)
    ; AT_15046.(gv) ].
Definition tyout_A1600____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1600____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_15042.(gv)
    ; LEN_15043.(gv)
    ; TRAIL_15044.(gv)
    ; AT_15046.(gv)
    ; w256_15047.(gv) ].

(* Body *)
Definition body_A1600____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15046) (Pvar CUR_15045)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15045) (Pconst (8)%Z)) (Pvar AT_15046))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15043) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15044) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_15047.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_15043))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_15048.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15046) (Pvar CUR_15045)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_15047.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_15040 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15041) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15042)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_15047.(gv) ] __SHLQ_256 [:: Pvar w256_15047
                                                                    ; Pvar AT8_15048 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15042.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15042) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15048))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15043.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15043) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15048))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_15046.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15045) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_15048.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15046) (Pvar CUR_15045)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_15042.(gv)
                                                                  ; Lvar LEN_15043.(gv)
                                                                  ; Lvar TRAIL_15044.(gv)
                                                                  ; Lvar AT_15046.(gv)
                                                                  ; Lvar w_15049.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_15040
                                                                    ; Pvar offset_15041
                                                                    ; Pvar DELTA_15042
                                                                    ; Pvar LEN_15043
                                                                    ; Pvar TRAIL_15044
                                                                    ; Pvar CUR_15045
                                                                    ; Pvar AT_15046 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_15050.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_15049)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_15047.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_15050 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_15047.(gv) ] __SHLQ_256 [:: Pvar w256_15047
                                                                    ; Pvar AT8_15048 ]) ]) ]) ].

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
