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

(* A1184____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_16209 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16209).
Definition offset_16210 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16210).
Definition DELTA_16211 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16211).
Definition LEN_16212 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16212).
Definition TRAIL_16213 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16213).
Definition CUR_16214 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16214).
Definition AT_16215 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16215).
Definition w_16216 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16216).
Definition AT32_16217 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16217).
Definition t128_0_16218 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16218).
Definition t128_1_16219 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16219).

(* Signature *)
Definition tyin_A1184____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 1184; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1184____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_16209.(gv)
    ; offset_16210.(gv)
    ; DELTA_16211.(gv)
    ; LEN_16212.(gv)
    ; TRAIL_16213.(gv)
    ; CUR_16214.(gv)
    ; AT_16215.(gv) ].
Definition tyout_A1184____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1184____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_16211.(gv)
    ; LEN_16212.(gv)
    ; TRAIL_16213.(gv)
    ; AT_16215.(gv)
    ; w_16216.(gv) ].

(* Body *)
Definition body_A1184____a_ilen_read_upto32_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_16215) (Pvar CUR_16214)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_16214) (Pconst (32)%Z)) (Pvar AT_16215))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_16212) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_16213) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_16216.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cassgn (Lvar AT32_16217.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_16215) (Pvar CUR_16214))
          ; cif
              (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_16217) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_16212)))
              [:: cassgn (Lvar w_16216.(gv)) (aword U256) (Pget Unaligned AAdirect U256 buf_16209 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16210) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16211)))))
                ; cassgn (Lvar AT32_16217.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_16217) (Pconst (32)%Z))
                ; cassgn (Lvar DELTA_16211.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16211) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_16212.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16212) (Pconst (32)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_16217))
                    [:: copn [:: Lvar w_16216.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::]
                      ; ccall [:: Lvar DELTA_16211.(gv)
                                ; Lvar LEN_16212.(gv)
                                ; Lvar TRAIL_16213.(gv)
                                ; Lvar AT32_16217.(gv)
                                ; Lvar t128_1_16219.(gv) ] A1184____a_ilen_read_upto16_at [:: Pvar buf_16209
                                                                    ; Pvar offset_16210
                                                                    ; Pvar DELTA_16211
                                                                    ; Pvar LEN_16212
                                                                    ; Pvar TRAIL_16213
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_16217 ]
                      ; copn [:: Lvar w_16216.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_16216
                                                                    ; Pvar t128_1_16219
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_16211.(gv)
                                ; Lvar LEN_16212.(gv)
                                ; Lvar TRAIL_16213.(gv)
                                ; Lvar AT32_16217.(gv)
                                ; Lvar t128_0_16218.(gv) ] A1184____a_ilen_read_upto16_at [:: Pvar buf_16209
                                                                    ; Pvar offset_16210
                                                                    ; Pvar DELTA_16211
                                                                    ; Pvar LEN_16212
                                                                    ; Pvar TRAIL_16213
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_16217 ]
                      ; ccall [:: Lvar DELTA_16211.(gv)
                                ; Lvar LEN_16212.(gv)
                                ; Lvar TRAIL_16213.(gv)
                                ; Lvar AT32_16217.(gv)
                                ; Lvar t128_1_16219.(gv) ] A1184____a_ilen_read_upto16_at [:: Pvar buf_16209
                                                                    ; Pvar offset_16210
                                                                    ; Pvar DELTA_16211
                                                                    ; Pvar LEN_16212
                                                                    ; Pvar TRAIL_16213
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_16217 ]
                      ; cassgn (Lvar w_16216.(gv)) (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_16219)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_16218) ]) ] ]
          ; cassgn (Lvar AT_16215.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_16214) (Pvar AT32_16217)) ] ].

Definition fd_A1184____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____a_ilen_read_upto32_at;
    f_params := args_A1184____a_ilen_read_upto32_at;
    f_body := body_A1184____a_ilen_read_upto32_at;
    f_tyout := tyout_A1184____a_ilen_read_upto32_at;
    f_res := res_A1184____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
