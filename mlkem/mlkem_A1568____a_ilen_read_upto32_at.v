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

(* A1568____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_15827 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15827).
Definition offset_15828 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15828).
Definition DELTA_15829 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15829).
Definition LEN_15830 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15830).
Definition TRAIL_15831 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15831).
Definition CUR_15832 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15832).
Definition AT_15833 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15833).
Definition w_15834 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15834).
Definition AT32_15835 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15835).
Definition t128_0_15836 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15836).
Definition t128_1_15837 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15837).

(* Signature *)
Definition tyin_A1568____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1568____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_15827.(gv)
    ; offset_15828.(gv)
    ; DELTA_15829.(gv)
    ; LEN_15830.(gv)
    ; TRAIL_15831.(gv)
    ; CUR_15832.(gv)
    ; AT_15833.(gv) ].
Definition tyout_A1568____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1568____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_15829.(gv)
    ; LEN_15830.(gv)
    ; TRAIL_15831.(gv)
    ; AT_15833.(gv)
    ; w_15834.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_read_upto32_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15833) (Pvar CUR_15832)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15832) (Pconst (32)%Z)) (Pvar AT_15833))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15830) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15831) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_15834.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cassgn (Lvar AT32_15835.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15833) (Pvar CUR_15832))
          ; cif
              (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_15835) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_15830)))
              [:: cassgn (Lvar w_15834.(gv)) (aword U256) (Pget Unaligned AAdirect U256 buf_15827 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15828) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15829)))))
                ; cassgn (Lvar AT32_15835.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_15835) (Pconst (32)%Z))
                ; cassgn (Lvar DELTA_15829.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15829) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_15830.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15830) (Pconst (32)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_15835))
                    [:: copn [:: Lvar w_15834.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::]
                      ; ccall [:: Lvar DELTA_15829.(gv)
                                ; Lvar LEN_15830.(gv)
                                ; Lvar TRAIL_15831.(gv)
                                ; Lvar AT32_15835.(gv)
                                ; Lvar t128_1_15837.(gv) ] A1568____a_ilen_read_upto16_at [:: Pvar buf_15827
                                                                    ; Pvar offset_15828
                                                                    ; Pvar DELTA_15829
                                                                    ; Pvar LEN_15830
                                                                    ; Pvar TRAIL_15831
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_15835 ]
                      ; copn [:: Lvar w_15834.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_15834
                                                                    ; Pvar t128_1_15837
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_15829.(gv)
                                ; Lvar LEN_15830.(gv)
                                ; Lvar TRAIL_15831.(gv)
                                ; Lvar AT32_15835.(gv)
                                ; Lvar t128_0_15836.(gv) ] A1568____a_ilen_read_upto16_at [:: Pvar buf_15827
                                                                    ; Pvar offset_15828
                                                                    ; Pvar DELTA_15829
                                                                    ; Pvar LEN_15830
                                                                    ; Pvar TRAIL_15831
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_15835 ]
                      ; ccall [:: Lvar DELTA_15829.(gv)
                                ; Lvar LEN_15830.(gv)
                                ; Lvar TRAIL_15831.(gv)
                                ; Lvar AT32_15835.(gv)
                                ; Lvar t128_1_15837.(gv) ] A1568____a_ilen_read_upto16_at [:: Pvar buf_15827
                                                                    ; Pvar offset_15828
                                                                    ; Pvar DELTA_15829
                                                                    ; Pvar LEN_15830
                                                                    ; Pvar TRAIL_15831
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_15835 ]
                      ; cassgn (Lvar w_15834.(gv)) (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_15837)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_15836) ]) ] ]
          ; cassgn (Lvar AT_15833.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15832) (Pvar AT32_15835)) ] ].

Definition fd_A1568____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_ilen_read_upto32_at;
    f_params := args_A1568____a_ilen_read_upto32_at;
    f_body := body_A1568____a_ilen_read_upto32_at;
    f_tyout := tyout_A1568____a_ilen_read_upto32_at;
    f_res := res_A1568____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
