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

(* A1____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_18389 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18389).
Definition offset_18390 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18390).
Definition DELTA_18391 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18391).
Definition LEN_18392 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18392).
Definition TRAIL_18393 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18393).
Definition CUR_18394 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18394).
Definition AT_18395 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18395).
Definition w_18396 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18396).
Definition AT16_18397 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18397).
Definition t64_0_18398 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18398).
Definition t64_1_18399 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18399).

(* Signature *)
Definition tyin_A1____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_18389.(gv)
    ; offset_18390.(gv)
    ; DELTA_18391.(gv)
    ; LEN_18392.(gv)
    ; TRAIL_18393.(gv)
    ; CUR_18394.(gv)
    ; AT_18395.(gv) ].
Definition tyout_A1____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A1____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_18391.(gv)
    ; LEN_18392.(gv)
    ; TRAIL_18393.(gv)
    ; AT_18395.(gv)
    ; w_18396.(gv) ].

(* Body *)
Definition body_A1____a_ilen_read_upto16_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_18395) (Pvar CUR_18394)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_18394) (Pconst (16)%Z)) (Pvar AT_18395))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_18392) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_18393) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_18396.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::] ]
        [:: cassgn (Lvar AT16_18397.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_18395) (Pvar CUR_18394))
          ; cif
              (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_18392))
              [:: cassgn (Lvar w_18396.(gv)) (aword U128) (Pget Unaligned AAdirect U128 buf_18389 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18390) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18391)))))
                ; ccall [:: Lvar w_18396.(gv) ] __SHLDQ [:: Pvar w_18396
                                                          ; Pvar AT16_18397 ]
                ; cassgn (Lvar DELTA_18391.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18391) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_18397)))
                ; cassgn (Lvar LEN_18392.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18392) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_18397)))
                ; cassgn (Lvar AT16_18397.(gv)) (aint) (Pconst (16)%Z) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_18397))
                    [:: copn [:: Lvar w_18396.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
                      ; ccall [:: Lvar DELTA_18391.(gv)
                                ; Lvar LEN_18392.(gv)
                                ; Lvar TRAIL_18393.(gv)
                                ; Lvar AT16_18397.(gv)
                                ; Lvar t64_1_18399.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_18389
                                                                    ; Pvar offset_18390
                                                                    ; Pvar DELTA_18391
                                                                    ; Pvar LEN_18392
                                                                    ; Pvar TRAIL_18393
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_18397 ]
                      ; copn [:: Lvar w_18396.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_18396
                                                                    ; Pvar t64_1_18399
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_18391.(gv)
                                ; Lvar LEN_18392.(gv)
                                ; Lvar TRAIL_18393.(gv)
                                ; Lvar AT16_18397.(gv)
                                ; Lvar t64_0_18398.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_18389
                                                                    ; Pvar offset_18390
                                                                    ; Pvar DELTA_18391
                                                                    ; Pvar LEN_18392
                                                                    ; Pvar TRAIL_18393
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_18397 ]
                      ; cassgn (Lvar w_18396.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_18398))
                      ; ccall [:: Lvar DELTA_18391.(gv)
                                ; Lvar LEN_18392.(gv)
                                ; Lvar TRAIL_18393.(gv)
                                ; Lvar AT16_18397.(gv)
                                ; Lvar t64_1_18399.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf_18389
                                                                    ; Pvar offset_18390
                                                                    ; Pvar DELTA_18391
                                                                    ; Pvar LEN_18392
                                                                    ; Pvar TRAIL_18393
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_18397 ]
                      ; copn [:: Lvar w_18396.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_18396
                                                                    ; Pvar t64_1_18399
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ] ]
          ; cassgn (Lvar AT_18395.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_18394) (Pvar AT16_18397)) ] ].

Definition fd_A1____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_ilen_read_upto16_at;
    f_params := args_A1____a_ilen_read_upto16_at;
    f_body := body_A1____a_ilen_read_upto16_at;
    f_tyout := tyout_A1____a_ilen_read_upto16_at;
    f_res := res_A1____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
