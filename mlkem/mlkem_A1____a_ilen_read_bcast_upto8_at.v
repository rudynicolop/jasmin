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

(* A1____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_18343 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18343).
Definition offset_18344 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18344).
Definition DELTA_18345 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18345).
Definition LEN_18346 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18346).
Definition TRAIL_18347 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18347).
Definition CUR_18348 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18348).
Definition AT_18349 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18349).
Definition w256_18350 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18350).
Definition AT8_18351 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18351).
Definition w_18352 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18352).
Definition t128_18353 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18353).

(* Signature *)
Definition tyin_A1____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_18343.(gv)
    ; offset_18344.(gv)
    ; DELTA_18345.(gv)
    ; LEN_18346.(gv)
    ; TRAIL_18347.(gv)
    ; CUR_18348.(gv)
    ; AT_18349.(gv) ].
Definition tyout_A1____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_18345.(gv)
    ; LEN_18346.(gv)
    ; TRAIL_18347.(gv)
    ; AT_18349.(gv)
    ; w256_18350.(gv) ].

(* Body *)
Definition body_A1____a_ilen_read_bcast_upto8_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_18349) (Pvar CUR_18348)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_18348) (Pconst (8)%Z)) (Pvar AT_18349))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_18346) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_18347) (Pconst (0)%Z))))
        [:: copn [:: Lvar w256_18350.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_18346))
              [:: cassgn (Lvar AT8_18351.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_18349) (Pvar CUR_18348))
                ; copn [:: Lvar w256_18350.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_18343 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18344) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18345)))) ]
                ; ccall [:: Lvar w256_18350.(gv) ] __SHLQ_256 [:: Pvar w256_18350
                                                                ; Pvar AT8_18351 ]
                ; cassgn (Lvar DELTA_18345.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18345) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18351)))
                ; cassgn (Lvar LEN_18346.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18346) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18351)))
                ; cassgn (Lvar AT_18349.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_18348) (Pconst (8)%Z)) ]
              [:: cassgn (Lvar AT8_18351.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_18349) (Pvar CUR_18348))
                ; ccall [:: Lvar DELTA_18345.(gv)
                          ; Lvar LEN_18346.(gv)
                          ; Lvar TRAIL_18347.(gv)
                          ; Lvar AT_18349.(gv)
                          ; Lvar w_18352.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_18343
                                                                    ; Pvar offset_18344
                                                                    ; Pvar DELTA_18345
                                                                    ; Pvar LEN_18346
                                                                    ; Pvar TRAIL_18347
                                                                    ; Pvar CUR_18348
                                                                    ; Pvar AT_18349 ]
                ; cassgn (Lvar t128_18353.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_18352))
                ; copn [:: Lvar w256_18350.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_18353 ]
                ; ccall [:: Lvar w256_18350.(gv) ] __SHLQ_256 [:: Pvar w256_18350
                                                                ; Pvar AT8_18351 ] ] ] ].

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
