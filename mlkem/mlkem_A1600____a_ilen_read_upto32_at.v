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

(* A1600____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_15063 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 15063).
Definition offset_15064 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15064).
Definition DELTA_15065 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15065).
Definition LEN_15066 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15066).
Definition TRAIL_15067 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15067).
Definition CUR_15068 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15068).
Definition AT_15069 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15069).
Definition w_15070 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15070).
Definition AT32_15071 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15071).
Definition t128_0_15072 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15072).
Definition t128_1_15073 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15073).

(* Signature *)
Definition tyin_A1600____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 1600; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1600____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_15063.(gv)
    ; offset_15064.(gv)
    ; DELTA_15065.(gv)
    ; LEN_15066.(gv)
    ; TRAIL_15067.(gv)
    ; CUR_15068.(gv)
    ; AT_15069.(gv) ].
Definition tyout_A1600____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1600____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_15065.(gv)
    ; LEN_15066.(gv)
    ; TRAIL_15067.(gv)
    ; AT_15069.(gv)
    ; w_15070.(gv) ].

(* Body *)
Definition body_A1600____a_ilen_read_upto32_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15069) (Pvar CUR_15068)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15068) (Pconst (32)%Z)) (Pvar AT_15069))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15066) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15067) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_15070.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cassgn (Lvar AT32_15071.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15069) (Pvar CUR_15068))
          ; cif
              (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_15071) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_15066)))
              [:: cassgn (Lvar w_15070.(gv)) (aword U256) (Pget Unaligned AAdirect U256 buf_15063 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15064) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15065)))))
                ; cassgn (Lvar AT32_15071.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_15071) (Pconst (32)%Z))
                ; cassgn (Lvar DELTA_15065.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15065) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_15066.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15066) (Pconst (32)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_15071))
                    [:: copn [:: Lvar w_15070.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::]
                      ; ccall [:: Lvar DELTA_15065.(gv)
                                ; Lvar LEN_15066.(gv)
                                ; Lvar TRAIL_15067.(gv)
                                ; Lvar AT32_15071.(gv)
                                ; Lvar t128_1_15073.(gv) ] A1600____a_ilen_read_upto16_at [:: Pvar buf_15063
                                                                    ; Pvar offset_15064
                                                                    ; Pvar DELTA_15065
                                                                    ; Pvar LEN_15066
                                                                    ; Pvar TRAIL_15067
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_15071 ]
                      ; copn [:: Lvar w_15070.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_15070
                                                                    ; Pvar t128_1_15073
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_15065.(gv)
                                ; Lvar LEN_15066.(gv)
                                ; Lvar TRAIL_15067.(gv)
                                ; Lvar AT32_15071.(gv)
                                ; Lvar t128_0_15072.(gv) ] A1600____a_ilen_read_upto16_at [:: Pvar buf_15063
                                                                    ; Pvar offset_15064
                                                                    ; Pvar DELTA_15065
                                                                    ; Pvar LEN_15066
                                                                    ; Pvar TRAIL_15067
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_15071 ]
                      ; ccall [:: Lvar DELTA_15065.(gv)
                                ; Lvar LEN_15066.(gv)
                                ; Lvar TRAIL_15067.(gv)
                                ; Lvar AT32_15071.(gv)
                                ; Lvar t128_1_15073.(gv) ] A1600____a_ilen_read_upto16_at [:: Pvar buf_15063
                                                                    ; Pvar offset_15064
                                                                    ; Pvar DELTA_15065
                                                                    ; Pvar LEN_15066
                                                                    ; Pvar TRAIL_15067
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_15071 ]
                      ; cassgn (Lvar w_15070.(gv)) (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_15073)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_15072) ]) ] ]
          ; cassgn (Lvar AT_15069.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15068) (Pvar AT32_15071)) ] ].

Definition fd_A1600____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____a_ilen_read_upto32_at;
    f_params := args_A1600____a_ilen_read_upto32_at;
    f_body := body_A1600____a_ilen_read_upto32_at;
    f_tyout := tyout_A1600____a_ilen_read_upto32_at;
    f_res := res_A1600____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
