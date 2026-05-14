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

(* A32____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_17579 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17579).
Definition offset_17580 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17580).
Definition DELTA_17581 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17581).
Definition LEN_17582 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17582).
Definition TRAIL_17583 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17583).
Definition CUR_17584 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17584).
Definition AT_17585 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17585).
Definition w256_17586 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17586).
Definition AT8_17587 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17587).
Definition w_17588 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17588).
Definition t128_17589 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17589).

(* Signature *)
Definition tyin_A32____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 32; aword U64; aint; aint; aint; aint; aint ].
Definition args_A32____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_17579.(gv)
    ; offset_17580.(gv)
    ; DELTA_17581.(gv)
    ; LEN_17582.(gv)
    ; TRAIL_17583.(gv)
    ; CUR_17584.(gv)
    ; AT_17585.(gv) ].
Definition tyout_A32____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A32____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_17581.(gv)
    ; LEN_17582.(gv)
    ; TRAIL_17583.(gv)
    ; AT_17585.(gv)
    ; w256_17586.(gv) ].

(* Body *)
Definition body_A32____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_17585) (Pvar CUR_17584)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_17584) (Pconst (8)%Z)) (Pvar AT_17585))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_17582) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_17583) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_17586.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_17582))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_17587.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17585) (Pvar CUR_17584)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_17586.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_17579 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17580) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17581)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_17586.(gv) ] __SHLQ_256 [:: Pvar w256_17586
                                                                    ; Pvar AT8_17587 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_17581.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17581) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17587))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_17582.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17582) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17587))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_17585.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_17584) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_17587.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17585) (Pvar CUR_17584)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_17581.(gv)
                                                                  ; Lvar LEN_17582.(gv)
                                                                  ; Lvar TRAIL_17583.(gv)
                                                                  ; Lvar AT_17585.(gv)
                                                                  ; Lvar w_17588.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_17579
                                                                    ; Pvar offset_17580
                                                                    ; Pvar DELTA_17581
                                                                    ; Pvar LEN_17582
                                                                    ; Pvar TRAIL_17583
                                                                    ; Pvar CUR_17584
                                                                    ; Pvar AT_17585 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_17589.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_17588)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_17586.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_17589 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_17586.(gv) ] __SHLQ_256 [:: Pvar w256_17586
                                                                    ; Pvar AT8_17587 ]) ]) ]) ].

Definition fd_A32____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____a_ilen_read_bcast_upto8_at;
    f_params := args_A32____a_ilen_read_bcast_upto8_at;
    f_body := body_A32____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A32____a_ilen_read_bcast_upto8_at;
    f_res := res_A32____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
