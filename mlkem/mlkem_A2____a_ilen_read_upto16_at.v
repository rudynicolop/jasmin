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

(* A2____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_18007 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 18007).
Definition offset_18008 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18008).
Definition DELTA_18009 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18009).
Definition LEN_18010 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18010).
Definition TRAIL_18011 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18011).
Definition CUR_18012 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18012).
Definition AT_18013 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18013).
Definition w_18014 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18014).
Definition AT16_18015 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18015).
Definition t64_0_18016 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18016).
Definition t64_1_18017 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18017).

(* Signature *)
Definition tyin_A2____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aint; aint; aint ].
Definition args_A2____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_18007.(gv)
    ; offset_18008.(gv)
    ; DELTA_18009.(gv)
    ; LEN_18010.(gv)
    ; TRAIL_18011.(gv)
    ; CUR_18012.(gv)
    ; AT_18013.(gv) ].
Definition tyout_A2____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A2____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_18009.(gv)
    ; LEN_18010.(gv)
    ; TRAIL_18011.(gv)
    ; AT_18013.(gv)
    ; w_18014.(gv) ].

(* Body *)
Definition body_A2____a_ilen_read_upto16_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_18013) (Pvar CUR_18012)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_18012) (Pconst (16)%Z)) (Pvar AT_18013))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_18010) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_18011) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_18014.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::] ]
        [:: cassgn (Lvar AT16_18015.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_18013) (Pvar CUR_18012))
          ; cif
              (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_18010))
              [:: cassgn (Lvar w_18014.(gv)) (aword U128) (Pget Unaligned AAdirect U128 buf_18007 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18008) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18009)))))
                ; ccall [:: Lvar w_18014.(gv) ] __SHLDQ [:: Pvar w_18014
                                                          ; Pvar AT16_18015 ]
                ; cassgn (Lvar DELTA_18009.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18009) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_18015)))
                ; cassgn (Lvar LEN_18010.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18010) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_18015)))
                ; cassgn (Lvar AT16_18015.(gv)) (aint) (Pconst (16)%Z) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_18015))
                    [:: copn [:: Lvar w_18014.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
                      ; ccall [:: Lvar DELTA_18009.(gv)
                                ; Lvar LEN_18010.(gv)
                                ; Lvar TRAIL_18011.(gv)
                                ; Lvar AT16_18015.(gv)
                                ; Lvar t64_1_18017.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_18007
                                                                    ; Pvar offset_18008
                                                                    ; Pvar DELTA_18009
                                                                    ; Pvar LEN_18010
                                                                    ; Pvar TRAIL_18011
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_18015 ]
                      ; copn [:: Lvar w_18014.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_18014
                                                                    ; Pvar t64_1_18017
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_18009.(gv)
                                ; Lvar LEN_18010.(gv)
                                ; Lvar TRAIL_18011.(gv)
                                ; Lvar AT16_18015.(gv)
                                ; Lvar t64_0_18016.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_18007
                                                                    ; Pvar offset_18008
                                                                    ; Pvar DELTA_18009
                                                                    ; Pvar LEN_18010
                                                                    ; Pvar TRAIL_18011
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_18015 ]
                      ; cassgn (Lvar w_18014.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_18016))
                      ; ccall [:: Lvar DELTA_18009.(gv)
                                ; Lvar LEN_18010.(gv)
                                ; Lvar TRAIL_18011.(gv)
                                ; Lvar AT16_18015.(gv)
                                ; Lvar t64_1_18017.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_18007
                                                                    ; Pvar offset_18008
                                                                    ; Pvar DELTA_18009
                                                                    ; Pvar LEN_18010
                                                                    ; Pvar TRAIL_18011
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_18015 ]
                      ; copn [:: Lvar w_18014.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_18014
                                                                    ; Pvar t64_1_18017
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ] ]
          ; cassgn (Lvar AT_18013.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_18012) (Pvar AT16_18015)) ] ].

Definition fd_A2____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_ilen_read_upto16_at;
    f_params := args_A2____a_ilen_read_upto16_at;
    f_body := body_A2____a_ilen_read_upto16_at;
    f_tyout := tyout_A2____a_ilen_read_upto16_at;
    f_res := res_A2____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
