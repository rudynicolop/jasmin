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

(* ABUFLEN____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_14704 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14704).
Definition offset_14705 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14705).
Definition DELTA_14706 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14706).
Definition LEN_14707 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14707).
Definition TRAIL_14708 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14708).
Definition CUR_14709 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14709).
Definition AT_14710 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14710).
Definition w_14711 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 14711).
Definition AT16_14712 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14712).
Definition t64_0_14713 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14713).
Definition t64_1_14714 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14714).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aint; aint; aint ].
Definition args_ABUFLEN____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_14704.(gv)
    ; offset_14705.(gv)
    ; DELTA_14706.(gv)
    ; LEN_14707.(gv)
    ; TRAIL_14708.(gv)
    ; CUR_14709.(gv)
    ; AT_14710.(gv) ].
Definition tyout_ABUFLEN____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_ABUFLEN____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_14706.(gv)
    ; LEN_14707.(gv)
    ; TRAIL_14708.(gv)
    ; AT_14710.(gv)
    ; w_14711.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_read_upto16_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_14710) (Pvar CUR_14709)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_14709) (Pconst (16)%Z)) (Pvar AT_14710))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_14707) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_14708) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_14711.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::] ]
        [:: cassgn (Lvar AT16_14712.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_14710) (Pvar CUR_14709))
          ; cif
              (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_14707))
              [:: cassgn (Lvar w_14711.(gv)) (aword U128) (Pget Unaligned AAdirect U128 buf_14704 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14705) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14706)))))
                ; ccall [:: Lvar w_14711.(gv) ] __SHLDQ [:: Pvar w_14711
                                                          ; Pvar AT16_14712 ]
                ; cassgn (Lvar DELTA_14706.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14706) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_14712)))
                ; cassgn (Lvar LEN_14707.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14707) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_14712)))
                ; cassgn (Lvar AT16_14712.(gv)) (aint) (Pconst (16)%Z) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_14712))
                    [:: copn [:: Lvar w_14711.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
                      ; ccall [:: Lvar DELTA_14706.(gv)
                                ; Lvar LEN_14707.(gv)
                                ; Lvar TRAIL_14708.(gv)
                                ; Lvar AT16_14712.(gv)
                                ; Lvar t64_1_14714.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_14704
                                                                    ; Pvar offset_14705
                                                                    ; Pvar DELTA_14706
                                                                    ; Pvar LEN_14707
                                                                    ; Pvar TRAIL_14708
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_14712 ]
                      ; copn [:: Lvar w_14711.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_14711
                                                                    ; Pvar t64_1_14714
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_14706.(gv)
                                ; Lvar LEN_14707.(gv)
                                ; Lvar TRAIL_14708.(gv)
                                ; Lvar AT16_14712.(gv)
                                ; Lvar t64_0_14713.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_14704
                                                                    ; Pvar offset_14705
                                                                    ; Pvar DELTA_14706
                                                                    ; Pvar LEN_14707
                                                                    ; Pvar TRAIL_14708
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_14712 ]
                      ; cassgn (Lvar w_14711.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_14713))
                      ; ccall [:: Lvar DELTA_14706.(gv)
                                ; Lvar LEN_14707.(gv)
                                ; Lvar TRAIL_14708.(gv)
                                ; Lvar AT16_14712.(gv)
                                ; Lvar t64_1_14714.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_14704
                                                                    ; Pvar offset_14705
                                                                    ; Pvar DELTA_14706
                                                                    ; Pvar LEN_14707
                                                                    ; Pvar TRAIL_14708
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_14712 ]
                      ; copn [:: Lvar w_14711.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_14711
                                                                    ; Pvar t64_1_14714
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ] ]
          ; cassgn (Lvar AT_14710.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_14709) (Pvar AT16_14712)) ] ].

Definition fd_ABUFLEN____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_read_upto16_at;
    f_params := args_ABUFLEN____a_ilen_read_upto16_at;
    f_body := body_ABUFLEN____a_ilen_read_upto16_at;
    f_tyout := tyout_ABUFLEN____a_ilen_read_upto16_at;
    f_res := res_ABUFLEN____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
