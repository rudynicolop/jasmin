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

(* A32____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_17625 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17625).
Definition offset_17626 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17626).
Definition DELTA_17627 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17627).
Definition LEN_17628 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17628).
Definition TRAIL_17629 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17629).
Definition CUR_17630 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17630).
Definition AT_17631 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17631).
Definition w_17632 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17632).
Definition AT16_17633 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17633).
Definition t64_0_17634 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17634).
Definition t64_1_17635 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17635).

(* Signature *)
Definition tyin_A32____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 32; aword U64; aint; aint; aint; aint; aint ].
Definition args_A32____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_17625.(gv)
    ; offset_17626.(gv)
    ; DELTA_17627.(gv)
    ; LEN_17628.(gv)
    ; TRAIL_17629.(gv)
    ; CUR_17630.(gv)
    ; AT_17631.(gv) ].
Definition tyout_A32____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A32____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_17627.(gv)
    ; LEN_17628.(gv)
    ; TRAIL_17629.(gv)
    ; AT_17631.(gv)
    ; w_17632.(gv) ].

(* Body *)
Definition body_A32____a_ilen_read_upto16_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_17631) (Pvar CUR_17630)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_17630) (Pconst (16)%Z)) (Pvar AT_17631))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_17628) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_17629) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_17632.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::] ]
        [:: cassgn (Lvar AT16_17633.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17631) (Pvar CUR_17630))
          ; cif
              (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_17628))
              [:: cassgn (Lvar w_17632.(gv)) (aword U128) (Pget Unaligned AAdirect U128 buf_17625 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17626) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17627)))))
                ; ccall [:: Lvar w_17632.(gv) ] __SHLDQ [:: Pvar w_17632
                                                          ; Pvar AT16_17633 ]
                ; cassgn (Lvar DELTA_17627.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17627) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_17633)))
                ; cassgn (Lvar LEN_17628.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17628) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_17633)))
                ; cassgn (Lvar AT16_17633.(gv)) (aint) (Pconst (16)%Z) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_17633))
                    [:: copn [:: Lvar w_17632.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
                      ; ccall [:: Lvar DELTA_17627.(gv)
                                ; Lvar LEN_17628.(gv)
                                ; Lvar TRAIL_17629.(gv)
                                ; Lvar AT16_17633.(gv)
                                ; Lvar t64_1_17635.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_17625
                                                                    ; Pvar offset_17626
                                                                    ; Pvar DELTA_17627
                                                                    ; Pvar LEN_17628
                                                                    ; Pvar TRAIL_17629
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_17633 ]
                      ; copn [:: Lvar w_17632.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_17632
                                                                    ; Pvar t64_1_17635
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_17627.(gv)
                                ; Lvar LEN_17628.(gv)
                                ; Lvar TRAIL_17629.(gv)
                                ; Lvar AT16_17633.(gv)
                                ; Lvar t64_0_17634.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_17625
                                                                    ; Pvar offset_17626
                                                                    ; Pvar DELTA_17627
                                                                    ; Pvar LEN_17628
                                                                    ; Pvar TRAIL_17629
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_17633 ]
                      ; cassgn (Lvar w_17632.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_17634))
                      ; ccall [:: Lvar DELTA_17627.(gv)
                                ; Lvar LEN_17628.(gv)
                                ; Lvar TRAIL_17629.(gv)
                                ; Lvar AT16_17633.(gv)
                                ; Lvar t64_1_17635.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf_17625
                                                                    ; Pvar offset_17626
                                                                    ; Pvar DELTA_17627
                                                                    ; Pvar LEN_17628
                                                                    ; Pvar TRAIL_17629
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_17633 ]
                      ; copn [:: Lvar w_17632.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_17632
                                                                    ; Pvar t64_1_17635
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ] ]
          ; cassgn (Lvar AT_17631.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_17630) (Pvar AT16_17633)) ] ].

Definition fd_A32____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____a_ilen_read_upto16_at;
    f_params := args_A32____a_ilen_read_upto16_at;
    f_body := body_A32____a_ilen_read_upto16_at;
    f_tyout := tyout_A32____a_ilen_read_upto16_at;
    f_res := res_A32____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
