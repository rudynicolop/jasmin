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

(* A1____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_18366 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18366).
Definition offset_18367 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18367).
Definition DELTA_18368 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18368).
Definition LEN_18369 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18369).
Definition TRAIL_18370 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18370).
Definition CUR_18371 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18371).
Definition AT_18372 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18372).
Definition w_18373 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18373).
Definition AT32_18374 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18374).
Definition t128_0_18375 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18375).
Definition t128_1_18376 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18376).

(* Signature *)
Definition tyin_A1____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_18366.(gv)
    ; offset_18367.(gv)
    ; DELTA_18368.(gv)
    ; LEN_18369.(gv)
    ; TRAIL_18370.(gv)
    ; CUR_18371.(gv)
    ; AT_18372.(gv) ].
Definition tyout_A1____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_18368.(gv)
    ; LEN_18369.(gv)
    ; TRAIL_18370.(gv)
    ; AT_18372.(gv)
    ; w_18373.(gv) ].

(* Body *)
Definition body_A1____a_ilen_read_upto32_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_18372) (Pvar CUR_18371)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_18371) (Pconst (32)%Z)) (Pvar AT_18372))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_18369) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_18370) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_18373.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cassgn (Lvar AT32_18374.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_18372) (Pvar CUR_18371))
          ; cif
              (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_18374) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_18369)))
              [:: cassgn (Lvar w_18373.(gv)) (aword U256) (Pget Unaligned AAdirect U256 buf_18366 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18367) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18368)))))
                ; cassgn (Lvar AT32_18374.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_18374) (Pconst (32)%Z))
                ; cassgn (Lvar DELTA_18368.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18368) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_18369.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18369) (Pconst (32)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_18374))
                    [:: copn [:: Lvar w_18373.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::]
                      ; ccall [:: Lvar DELTA_18368.(gv)
                                ; Lvar LEN_18369.(gv)
                                ; Lvar TRAIL_18370.(gv)
                                ; Lvar AT32_18374.(gv)
                                ; Lvar t128_1_18376.(gv) ] A1____a_ilen_read_upto16_at [:: Pvar buf_18366
                                                                    ; Pvar offset_18367
                                                                    ; Pvar DELTA_18368
                                                                    ; Pvar LEN_18369
                                                                    ; Pvar TRAIL_18370
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_18374 ]
                      ; copn [:: Lvar w_18373.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_18373
                                                                    ; Pvar t128_1_18376
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_18368.(gv)
                                ; Lvar LEN_18369.(gv)
                                ; Lvar TRAIL_18370.(gv)
                                ; Lvar AT32_18374.(gv)
                                ; Lvar t128_0_18375.(gv) ] A1____a_ilen_read_upto16_at [:: Pvar buf_18366
                                                                    ; Pvar offset_18367
                                                                    ; Pvar DELTA_18368
                                                                    ; Pvar LEN_18369
                                                                    ; Pvar TRAIL_18370
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_18374 ]
                      ; ccall [:: Lvar DELTA_18368.(gv)
                                ; Lvar LEN_18369.(gv)
                                ; Lvar TRAIL_18370.(gv)
                                ; Lvar AT32_18374.(gv)
                                ; Lvar t128_1_18376.(gv) ] A1____a_ilen_read_upto16_at [:: Pvar buf_18366
                                                                    ; Pvar offset_18367
                                                                    ; Pvar DELTA_18368
                                                                    ; Pvar LEN_18369
                                                                    ; Pvar TRAIL_18370
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_18374 ]
                      ; cassgn (Lvar w_18373.(gv)) (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_18376)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_18375) ]) ] ]
          ; cassgn (Lvar AT_18372.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_18371) (Pvar AT32_18374)) ] ].

Definition fd_A1____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_ilen_read_upto32_at;
    f_params := args_A1____a_ilen_read_upto32_at;
    f_body := body_A1____a_ilen_read_upto32_at;
    f_tyout := tyout_A1____a_ilen_read_upto32_at;
    f_res := res_A1____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
