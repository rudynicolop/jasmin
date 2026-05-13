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

(* ABUFLEN____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_14681 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14681).
Definition offset_14682 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14682).
Definition DELTA_14683 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14683).
Definition LEN_14684 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14684).
Definition TRAIL_14685 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14685).
Definition CUR_14686 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14686).
Definition AT_14687 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14687).
Definition w_14688 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14688).
Definition AT32_14689 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14689).
Definition t128_0_14690 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14690).
Definition t128_1_14691 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14691).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aint; aint; aint ].
Definition args_ABUFLEN____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_14681.(gv)
    ; offset_14682.(gv)
    ; DELTA_14683.(gv)
    ; LEN_14684.(gv)
    ; TRAIL_14685.(gv)
    ; CUR_14686.(gv)
    ; AT_14687.(gv) ].
Definition tyout_ABUFLEN____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_ABUFLEN____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_14683.(gv)
    ; LEN_14684.(gv)
    ; TRAIL_14685.(gv)
    ; AT_14687.(gv)
    ; w_14688.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_read_upto32_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_14687) (Pvar CUR_14686)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_14686) (Pconst (32)%Z)) (Pvar AT_14687))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_14684) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_14685) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_14688.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cassgn (Lvar AT32_14689.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_14687) (Pvar CUR_14686))
          ; cif
              (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_14689) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_14684)))
              [:: cassgn (Lvar w_14688.(gv)) (aword U256) (Pget Unaligned AAdirect U256 buf_14681 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14682) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14683)))))
                ; cassgn (Lvar AT32_14689.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_14689) (Pconst (32)%Z))
                ; cassgn (Lvar DELTA_14683.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14683) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_14684.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14684) (Pconst (32)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_14689))
                    [:: copn [:: Lvar w_14688.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::]
                      ; ccall [:: Lvar DELTA_14683.(gv)
                                ; Lvar LEN_14684.(gv)
                                ; Lvar TRAIL_14685.(gv)
                                ; Lvar AT32_14689.(gv)
                                ; Lvar t128_1_14691.(gv) ] ABUFLEN____a_ilen_read_upto16_at [:: Pvar buf_14681
                                                                    ; Pvar offset_14682
                                                                    ; Pvar DELTA_14683
                                                                    ; Pvar LEN_14684
                                                                    ; Pvar TRAIL_14685
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_14689 ]
                      ; copn [:: Lvar w_14688.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_14688
                                                                    ; Pvar t128_1_14691
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_14683.(gv)
                                ; Lvar LEN_14684.(gv)
                                ; Lvar TRAIL_14685.(gv)
                                ; Lvar AT32_14689.(gv)
                                ; Lvar t128_0_14690.(gv) ] ABUFLEN____a_ilen_read_upto16_at [:: Pvar buf_14681
                                                                    ; Pvar offset_14682
                                                                    ; Pvar DELTA_14683
                                                                    ; Pvar LEN_14684
                                                                    ; Pvar TRAIL_14685
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_14689 ]
                      ; ccall [:: Lvar DELTA_14683.(gv)
                                ; Lvar LEN_14684.(gv)
                                ; Lvar TRAIL_14685.(gv)
                                ; Lvar AT32_14689.(gv)
                                ; Lvar t128_1_14691.(gv) ] ABUFLEN____a_ilen_read_upto16_at [:: Pvar buf_14681
                                                                    ; Pvar offset_14682
                                                                    ; Pvar DELTA_14683
                                                                    ; Pvar LEN_14684
                                                                    ; Pvar TRAIL_14685
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_14689 ]
                      ; cassgn (Lvar w_14688.(gv)) (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_14691)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_14690) ]) ] ]
          ; cassgn (Lvar AT_14687.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_14686) (Pvar AT32_14689)) ] ].

Definition fd_ABUFLEN____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_read_upto32_at;
    f_params := args_ABUFLEN____a_ilen_read_upto32_at;
    f_body := body_ABUFLEN____a_ilen_read_upto32_at;
    f_tyout := tyout_ABUFLEN____a_ilen_read_upto32_at;
    f_res := res_ABUFLEN____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
