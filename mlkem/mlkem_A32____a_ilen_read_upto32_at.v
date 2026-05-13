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

(* A32____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_17602 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17602).
Definition offset_17603 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17603).
Definition DELTA_17604 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17604).
Definition LEN_17605 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17605).
Definition TRAIL_17606 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17606).
Definition CUR_17607 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17607).
Definition AT_17608 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17608).
Definition w_17609 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17609).
Definition AT32_17610 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17610).
Definition t128_0_17611 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17611).
Definition t128_1_17612 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17612).

(* Signature *)
Definition tyin_A32____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 32; aword U64; aint; aint; aint; aint; aint ].
Definition args_A32____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_17602.(gv)
    ; offset_17603.(gv)
    ; DELTA_17604.(gv)
    ; LEN_17605.(gv)
    ; TRAIL_17606.(gv)
    ; CUR_17607.(gv)
    ; AT_17608.(gv) ].
Definition tyout_A32____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A32____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_17604.(gv)
    ; LEN_17605.(gv)
    ; TRAIL_17606.(gv)
    ; AT_17608.(gv)
    ; w_17609.(gv) ].

(* Body *)
Definition body_A32____a_ilen_read_upto32_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_17608) (Pvar CUR_17607)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_17607) (Pconst (32)%Z)) (Pvar AT_17608))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_17605) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_17606) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_17609.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cassgn (Lvar AT32_17610.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17608) (Pvar CUR_17607))
          ; cif
              (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_17610) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_17605)))
              [:: cassgn (Lvar w_17609.(gv)) (aword U256) (Pget Unaligned AAdirect U256 buf_17602 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17603) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17604)))))
                ; cassgn (Lvar AT32_17610.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_17610) (Pconst (32)%Z))
                ; cassgn (Lvar DELTA_17604.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17604) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_17605.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17605) (Pconst (32)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_17610))
                    [:: copn [:: Lvar w_17609.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::]
                      ; ccall [:: Lvar DELTA_17604.(gv)
                                ; Lvar LEN_17605.(gv)
                                ; Lvar TRAIL_17606.(gv)
                                ; Lvar AT32_17610.(gv)
                                ; Lvar t128_1_17612.(gv) ] A32____a_ilen_read_upto16_at [:: Pvar buf_17602
                                                                    ; Pvar offset_17603
                                                                    ; Pvar DELTA_17604
                                                                    ; Pvar LEN_17605
                                                                    ; Pvar TRAIL_17606
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_17610 ]
                      ; copn [:: Lvar w_17609.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_17609
                                                                    ; Pvar t128_1_17612
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_17604.(gv)
                                ; Lvar LEN_17605.(gv)
                                ; Lvar TRAIL_17606.(gv)
                                ; Lvar AT32_17610.(gv)
                                ; Lvar t128_0_17611.(gv) ] A32____a_ilen_read_upto16_at [:: Pvar buf_17602
                                                                    ; Pvar offset_17603
                                                                    ; Pvar DELTA_17604
                                                                    ; Pvar LEN_17605
                                                                    ; Pvar TRAIL_17606
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_17610 ]
                      ; ccall [:: Lvar DELTA_17604.(gv)
                                ; Lvar LEN_17605.(gv)
                                ; Lvar TRAIL_17606.(gv)
                                ; Lvar AT32_17610.(gv)
                                ; Lvar t128_1_17612.(gv) ] A32____a_ilen_read_upto16_at [:: Pvar buf_17602
                                                                    ; Pvar offset_17603
                                                                    ; Pvar DELTA_17604
                                                                    ; Pvar LEN_17605
                                                                    ; Pvar TRAIL_17606
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_17610 ]
                      ; cassgn (Lvar w_17609.(gv)) (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_17612)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_17611) ]) ] ]
          ; cassgn (Lvar AT_17608.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_17607) (Pvar AT32_17610)) ] ].

Definition fd_A32____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____a_ilen_read_upto32_at;
    f_params := args_A32____a_ilen_read_upto32_at;
    f_body := body_A32____a_ilen_read_upto32_at;
    f_tyout := tyout_A32____a_ilen_read_upto32_at;
    f_res := res_A32____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
