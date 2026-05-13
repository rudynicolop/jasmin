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

(* A64____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_16861 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 16861).
Definition offset_16862 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16862).
Definition DELTA_16863 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16863).
Definition LEN_16864 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16864).
Definition TRAIL_16865 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16865).
Definition CUR_16866 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16866).
Definition AT_16867 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16867).
Definition w_16868 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16868).
Definition AT16_16869 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16869).
Definition t64_0_16870 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16870).
Definition t64_1_16871 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16871).

(* Signature *)
Definition tyin_A64____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 64; aword U64; aint; aint; aint; aint; aint ].
Definition args_A64____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_16861.(gv)
    ; offset_16862.(gv)
    ; DELTA_16863.(gv)
    ; LEN_16864.(gv)
    ; TRAIL_16865.(gv)
    ; CUR_16866.(gv)
    ; AT_16867.(gv) ].
Definition tyout_A64____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A64____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_16863.(gv)
    ; LEN_16864.(gv)
    ; TRAIL_16865.(gv)
    ; AT_16867.(gv)
    ; w_16868.(gv) ].

(* Body *)
Definition body_A64____a_ilen_read_upto16_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_16867) (Pvar CUR_16866)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_16866) (Pconst (16)%Z)) (Pvar AT_16867))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_16864) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_16865) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_16868.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::] ]
        [:: cassgn (Lvar AT16_16869.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_16867) (Pvar CUR_16866))
          ; cif
              (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_16864))
              [:: cassgn (Lvar w_16868.(gv)) (aword U128) (Pget Unaligned AAdirect U128 buf_16861 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16862) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16863)))))
                ; ccall [:: Lvar w_16868.(gv) ] __SHLDQ [:: Pvar w_16868
                                                          ; Pvar AT16_16869 ]
                ; cassgn (Lvar DELTA_16863.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16863) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_16869)))
                ; cassgn (Lvar LEN_16864.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16864) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_16869)))
                ; cassgn (Lvar AT16_16869.(gv)) (aint) (Pconst (16)%Z) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_16869))
                    [:: copn [:: Lvar w_16868.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
                      ; ccall [:: Lvar DELTA_16863.(gv)
                                ; Lvar LEN_16864.(gv)
                                ; Lvar TRAIL_16865.(gv)
                                ; Lvar AT16_16869.(gv)
                                ; Lvar t64_1_16871.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_16861
                                                                    ; Pvar offset_16862
                                                                    ; Pvar DELTA_16863
                                                                    ; Pvar LEN_16864
                                                                    ; Pvar TRAIL_16865
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_16869 ]
                      ; copn [:: Lvar w_16868.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_16868
                                                                    ; Pvar t64_1_16871
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_16863.(gv)
                                ; Lvar LEN_16864.(gv)
                                ; Lvar TRAIL_16865.(gv)
                                ; Lvar AT16_16869.(gv)
                                ; Lvar t64_0_16870.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_16861
                                                                    ; Pvar offset_16862
                                                                    ; Pvar DELTA_16863
                                                                    ; Pvar LEN_16864
                                                                    ; Pvar TRAIL_16865
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_16869 ]
                      ; cassgn (Lvar w_16868.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_16870))
                      ; ccall [:: Lvar DELTA_16863.(gv)
                                ; Lvar LEN_16864.(gv)
                                ; Lvar TRAIL_16865.(gv)
                                ; Lvar AT16_16869.(gv)
                                ; Lvar t64_1_16871.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_16861
                                                                    ; Pvar offset_16862
                                                                    ; Pvar DELTA_16863
                                                                    ; Pvar LEN_16864
                                                                    ; Pvar TRAIL_16865
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_16869 ]
                      ; copn [:: Lvar w_16868.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_16868
                                                                    ; Pvar t64_1_16871
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ] ]
          ; cassgn (Lvar AT_16867.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_16866) (Pvar AT16_16869)) ] ].

Definition fd_A64____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_ilen_read_upto16_at;
    f_params := args_A64____a_ilen_read_upto16_at;
    f_body := body_A64____a_ilen_read_upto16_at;
    f_tyout := tyout_A64____a_ilen_read_upto16_at;
    f_res := res_A64____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
