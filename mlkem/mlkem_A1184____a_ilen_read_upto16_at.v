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

(* A1184____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_16232 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16232).
Definition offset_16233 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16233).
Definition DELTA_16234 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16234).
Definition LEN_16235 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16235).
Definition TRAIL_16236 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16236).
Definition CUR_16237 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16237).
Definition AT_16238 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16238).
Definition w_16239 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16239).
Definition AT16_16240 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16240).
Definition t64_0_16241 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16241).
Definition t64_1_16242 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16242).

(* Signature *)
Definition tyin_A1184____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 1184; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1184____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_16232.(gv)
    ; offset_16233.(gv)
    ; DELTA_16234.(gv)
    ; LEN_16235.(gv)
    ; TRAIL_16236.(gv)
    ; CUR_16237.(gv)
    ; AT_16238.(gv) ].
Definition tyout_A1184____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A1184____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_16234.(gv)
    ; LEN_16235.(gv)
    ; TRAIL_16236.(gv)
    ; AT_16238.(gv)
    ; w_16239.(gv) ].

(* Body *)
Definition body_A1184____a_ilen_read_upto16_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_16238) (Pvar CUR_16237)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_16237) (Pconst (16)%Z)) (Pvar AT_16238))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_16235) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_16236) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_16239.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::] ]
        [:: cassgn (Lvar AT16_16240.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_16238) (Pvar CUR_16237))
          ; cif
              (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_16235))
              [:: cassgn (Lvar w_16239.(gv)) (aword U128) (Pget Unaligned AAdirect U128 buf_16232 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16233) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16234)))))
                ; ccall [:: Lvar w_16239.(gv) ] __SHLDQ [:: Pvar w_16239
                                                          ; Pvar AT16_16240 ]
                ; cassgn (Lvar DELTA_16234.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16234) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_16240)))
                ; cassgn (Lvar LEN_16235.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16235) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_16240)))
                ; cassgn (Lvar AT16_16240.(gv)) (aint) (Pconst (16)%Z) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_16240))
                    [:: copn [:: Lvar w_16239.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
                      ; ccall [:: Lvar DELTA_16234.(gv)
                                ; Lvar LEN_16235.(gv)
                                ; Lvar TRAIL_16236.(gv)
                                ; Lvar AT16_16240.(gv)
                                ; Lvar t64_1_16242.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_16232
                                                                    ; Pvar offset_16233
                                                                    ; Pvar DELTA_16234
                                                                    ; Pvar LEN_16235
                                                                    ; Pvar TRAIL_16236
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_16240 ]
                      ; copn [:: Lvar w_16239.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_16239
                                                                    ; Pvar t64_1_16242
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_16234.(gv)
                                ; Lvar LEN_16235.(gv)
                                ; Lvar TRAIL_16236.(gv)
                                ; Lvar AT16_16240.(gv)
                                ; Lvar t64_0_16241.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_16232
                                                                    ; Pvar offset_16233
                                                                    ; Pvar DELTA_16234
                                                                    ; Pvar LEN_16235
                                                                    ; Pvar TRAIL_16236
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_16240 ]
                      ; cassgn (Lvar w_16239.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_16241))
                      ; ccall [:: Lvar DELTA_16234.(gv)
                                ; Lvar LEN_16235.(gv)
                                ; Lvar TRAIL_16236.(gv)
                                ; Lvar AT16_16240.(gv)
                                ; Lvar t64_1_16242.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_16232
                                                                    ; Pvar offset_16233
                                                                    ; Pvar DELTA_16234
                                                                    ; Pvar LEN_16235
                                                                    ; Pvar TRAIL_16236
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_16240 ]
                      ; copn [:: Lvar w_16239.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_16239
                                                                    ; Pvar t64_1_16242
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ] ]
          ; cassgn (Lvar AT_16238.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_16237) (Pvar AT16_16240)) ] ].

Definition fd_A1184____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____a_ilen_read_upto16_at;
    f_params := args_A1184____a_ilen_read_upto16_at;
    f_body := body_A1184____a_ilen_read_upto16_at;
    f_tyout := tyout_A1184____a_ilen_read_upto16_at;
    f_res := res_A1184____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
