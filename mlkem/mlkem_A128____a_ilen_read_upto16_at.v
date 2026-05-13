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

(* A128____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_16614 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16614).
Definition offset_16615 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16615).
Definition DELTA_16616 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16616).
Definition LEN_16617 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16617).
Definition TRAIL_16618 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16618).
Definition CUR_16619 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16619).
Definition AT_16620 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16620).
Definition w_16621 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16621).
Definition AT16_16622 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16622).
Definition t64_0_16623 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16623).
Definition t64_1_16624 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16624).

(* Signature *)
Definition tyin_A128____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 128; aword U64; aint; aint; aint; aint; aint ].
Definition args_A128____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_16614.(gv)
    ; offset_16615.(gv)
    ; DELTA_16616.(gv)
    ; LEN_16617.(gv)
    ; TRAIL_16618.(gv)
    ; CUR_16619.(gv)
    ; AT_16620.(gv) ].
Definition tyout_A128____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A128____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_16616.(gv)
    ; LEN_16617.(gv)
    ; TRAIL_16618.(gv)
    ; AT_16620.(gv)
    ; w_16621.(gv) ].

(* Body *)
Definition body_A128____a_ilen_read_upto16_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_16620) (Pvar CUR_16619)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_16619) (Pconst (16)%Z)) (Pvar AT_16620))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_16617) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_16618) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_16621.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::] ]
        [:: cassgn (Lvar AT16_16622.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_16620) (Pvar CUR_16619))
          ; cif
              (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_16617))
              [:: cassgn (Lvar w_16621.(gv)) (aword U128) (Pget Unaligned AAdirect U128 buf_16614 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16615) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16616)))))
                ; ccall [:: Lvar w_16621.(gv) ] __SHLDQ [:: Pvar w_16621
                                                          ; Pvar AT16_16622 ]
                ; cassgn (Lvar DELTA_16616.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16616) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_16622)))
                ; cassgn (Lvar LEN_16617.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16617) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_16622)))
                ; cassgn (Lvar AT16_16622.(gv)) (aint) (Pconst (16)%Z) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_16622))
                    [:: copn [:: Lvar w_16621.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
                      ; ccall [:: Lvar DELTA_16616.(gv)
                                ; Lvar LEN_16617.(gv)
                                ; Lvar TRAIL_16618.(gv)
                                ; Lvar AT16_16622.(gv)
                                ; Lvar t64_1_16624.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_16614
                                                                    ; Pvar offset_16615
                                                                    ; Pvar DELTA_16616
                                                                    ; Pvar LEN_16617
                                                                    ; Pvar TRAIL_16618
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_16622 ]
                      ; copn [:: Lvar w_16621.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_16621
                                                                    ; Pvar t64_1_16624
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_16616.(gv)
                                ; Lvar LEN_16617.(gv)
                                ; Lvar TRAIL_16618.(gv)
                                ; Lvar AT16_16622.(gv)
                                ; Lvar t64_0_16623.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_16614
                                                                    ; Pvar offset_16615
                                                                    ; Pvar DELTA_16616
                                                                    ; Pvar LEN_16617
                                                                    ; Pvar TRAIL_16618
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_16622 ]
                      ; cassgn (Lvar w_16621.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_16623))
                      ; ccall [:: Lvar DELTA_16616.(gv)
                                ; Lvar LEN_16617.(gv)
                                ; Lvar TRAIL_16618.(gv)
                                ; Lvar AT16_16622.(gv)
                                ; Lvar t64_1_16624.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_16614
                                                                    ; Pvar offset_16615
                                                                    ; Pvar DELTA_16616
                                                                    ; Pvar LEN_16617
                                                                    ; Pvar TRAIL_16618
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_16622 ]
                      ; copn [:: Lvar w_16621.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_16621
                                                                    ; Pvar t64_1_16624
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ] ]
          ; cassgn (Lvar AT_16620.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_16619) (Pvar AT16_16622)) ] ].

Definition fd_A128____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____a_ilen_read_upto16_at;
    f_params := args_A128____a_ilen_read_upto16_at;
    f_body := body_A128____a_ilen_read_upto16_at;
    f_tyout := tyout_A128____a_ilen_read_upto16_at;
    f_res := res_A128____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
