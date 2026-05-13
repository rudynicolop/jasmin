From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* A128____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_16568 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16568).
Definition offset_16569 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16569).
Definition DELTA_16570 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16570).
Definition LEN_16571 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16571).
Definition TRAIL_16572 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16572).
Definition CUR_16573 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16573).
Definition AT_16574 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16574).
Definition w256_16575 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16575).
Definition AT8_16576 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16576).
Definition w_16577 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16577).
Definition t128_16578 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16578).

(* Signature *)
Definition tyin_A128____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 128; aword U64; aint; aint; aint; aint; aint ].
Definition args_A128____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_16568.(gv)
    ; offset_16569.(gv)
    ; DELTA_16570.(gv)
    ; LEN_16571.(gv)
    ; TRAIL_16572.(gv)
    ; CUR_16573.(gv)
    ; AT_16574.(gv) ].
Definition tyout_A128____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A128____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_16570.(gv)
    ; LEN_16571.(gv)
    ; TRAIL_16572.(gv)
    ; AT_16574.(gv)
    ; w256_16575.(gv) ].

(* Body *)
Definition body_A128____a_ilen_read_bcast_upto8_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_16574) (Pvar CUR_16573)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_16573) (Pconst (8)%Z)) (Pvar AT_16574))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_16571) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_16572) (Pconst (0)%Z))))
        [:: copn [:: Lvar w256_16575.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_16571))
              [:: cassgn (Lvar AT8_16576.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_16574) (Pvar CUR_16573))
                ; copn [:: Lvar w256_16575.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_16568 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16569) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16570)))) ]
                ; ccall [:: Lvar w256_16575.(gv) ] __SHLQ_256 [:: Pvar w256_16575
                                                                ; Pvar AT8_16576 ]
                ; cassgn (Lvar DELTA_16570.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16570) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16576)))
                ; cassgn (Lvar LEN_16571.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16571) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16576)))
                ; cassgn (Lvar AT_16574.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_16573) (Pconst (8)%Z)) ]
              [:: cassgn (Lvar AT8_16576.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_16574) (Pvar CUR_16573))
                ; ccall [:: Lvar DELTA_16570.(gv)
                          ; Lvar LEN_16571.(gv)
                          ; Lvar TRAIL_16572.(gv)
                          ; Lvar AT_16574.(gv)
                          ; Lvar w_16577.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_16568
                                                                    ; Pvar offset_16569
                                                                    ; Pvar DELTA_16570
                                                                    ; Pvar LEN_16571
                                                                    ; Pvar TRAIL_16572
                                                                    ; Pvar CUR_16573
                                                                    ; Pvar AT_16574 ]
                ; cassgn (Lvar t128_16578.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_16577))
                ; copn [:: Lvar w256_16575.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_16578 ]
                ; ccall [:: Lvar w256_16575.(gv) ] __SHLQ_256 [:: Pvar w256_16575
                                                                ; Pvar AT8_16576 ] ] ] ].

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
