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

(* A128____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_85 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16568).
Definition offset_81 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16569).
Definition DELTA_55 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16570).
Definition LEN_44 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16571).
Definition TRAIL_26 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16572).
Definition CUR_26 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16573).
Definition AT_58 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16574).
Definition w256_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16575).
Definition AT8_22 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16576).
Definition w_60 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16577).
Definition t128_13 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16578).

(* Signature *)
Definition tyin_A128____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 128; aword U64; aint; aint; aint; aint; aint ].
Definition args_A128____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_85.(gv)
    ; offset_81.(gv)
    ; DELTA_55.(gv)
    ; LEN_44.(gv)
    ; TRAIL_26.(gv)
    ; CUR_26.(gv)
    ; AT_58.(gv) ].
Definition tyout_A128____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A128____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_55.(gv); LEN_44.(gv); TRAIL_26.(gv); AT_58.(gv); w256_5.(gv) ].

(* Body *)
Definition body_A128____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_58) (Pvar CUR_26)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_26) (Pconst (8)%Z)) (Pvar AT_58))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_44) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_26) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_5.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_44))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_22.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_58) (Pvar CUR_26)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_85 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_81) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_55)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_5.(gv) ] __SHLQ_256 [:: Pvar w256_5
                                                                    ; Pvar AT8_22 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_55.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_55) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_22))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_44.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_44) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_22))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_58.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_26) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_22.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_58) (Pvar CUR_26)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_55.(gv)
                                                                  ; Lvar LEN_44.(gv)
                                                                  ; Lvar TRAIL_26.(gv)
                                                                  ; Lvar AT_58.(gv)
                                                                  ; Lvar w_60.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_85
                                                                    ; Pvar offset_81
                                                                    ; Pvar DELTA_55
                                                                    ; Pvar LEN_44
                                                                    ; Pvar TRAIL_26
                                                                    ; Pvar CUR_26
                                                                    ; Pvar AT_58 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_13.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_60)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_13 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_5.(gv) ] __SHLQ_256 [:: Pvar w256_5
                                                                    ; Pvar AT8_22 ]) ]) ]) ].

Definition fd_A128____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____a_ilen_read_bcast_upto8_at;
    f_params := args_A128____a_ilen_read_bcast_upto8_at;
    f_body := body_A128____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A128____a_ilen_read_bcast_upto8_at;
    f_res := res_A128____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
