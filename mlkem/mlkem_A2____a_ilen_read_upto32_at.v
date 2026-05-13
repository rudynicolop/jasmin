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

(* A2____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_17984 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17984).
Definition offset_17985 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17985).
Definition DELTA_17986 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17986).
Definition LEN_17987 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17987).
Definition TRAIL_17988 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17988).
Definition CUR_17989 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17989).
Definition AT_17990 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17990).
Definition w_17991 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17991).
Definition AT32_17992 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17992).
Definition t128_0_17993 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17993).
Definition t128_1_17994 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17994).

(* Signature *)
Definition tyin_A2____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aint; aint; aint ].
Definition args_A2____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_17984.(gv)
    ; offset_17985.(gv)
    ; DELTA_17986.(gv)
    ; LEN_17987.(gv)
    ; TRAIL_17988.(gv)
    ; CUR_17989.(gv)
    ; AT_17990.(gv) ].
Definition tyout_A2____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A2____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_17986.(gv)
    ; LEN_17987.(gv)
    ; TRAIL_17988.(gv)
    ; AT_17990.(gv)
    ; w_17991.(gv) ].

(* Body *)
Definition body_A2____a_ilen_read_upto32_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_17990) (Pvar CUR_17989)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_17989) (Pconst (32)%Z)) (Pvar AT_17990))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_17987) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_17988) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_17991.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cassgn (Lvar AT32_17992.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17990) (Pvar CUR_17989))
          ; cif
              (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_17992) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_17987)))
              [:: cassgn (Lvar w_17991.(gv)) (aword U256) (Pget Unaligned AAdirect U256 buf_17984 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17985) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17986)))))
                ; cassgn (Lvar AT32_17992.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_17992) (Pconst (32)%Z))
                ; cassgn (Lvar DELTA_17986.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17986) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_17987.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17987) (Pconst (32)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_17992))
                    [:: copn [:: Lvar w_17991.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::]
                      ; ccall [:: Lvar DELTA_17986.(gv)
                                ; Lvar LEN_17987.(gv)
                                ; Lvar TRAIL_17988.(gv)
                                ; Lvar AT32_17992.(gv)
                                ; Lvar t128_1_17994.(gv) ] A2____a_ilen_read_upto16_at [:: Pvar buf_17984
                                                                    ; Pvar offset_17985
                                                                    ; Pvar DELTA_17986
                                                                    ; Pvar LEN_17987
                                                                    ; Pvar TRAIL_17988
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_17992 ]
                      ; copn [:: Lvar w_17991.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_17991
                                                                    ; Pvar t128_1_17994
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar DELTA_17986.(gv)
                                ; Lvar LEN_17987.(gv)
                                ; Lvar TRAIL_17988.(gv)
                                ; Lvar AT32_17992.(gv)
                                ; Lvar t128_0_17993.(gv) ] A2____a_ilen_read_upto16_at [:: Pvar buf_17984
                                                                    ; Pvar offset_17985
                                                                    ; Pvar DELTA_17986
                                                                    ; Pvar LEN_17987
                                                                    ; Pvar TRAIL_17988
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_17992 ]
                      ; ccall [:: Lvar DELTA_17986.(gv)
                                ; Lvar LEN_17987.(gv)
                                ; Lvar TRAIL_17988.(gv)
                                ; Lvar AT32_17992.(gv)
                                ; Lvar t128_1_17994.(gv) ] A2____a_ilen_read_upto16_at [:: Pvar buf_17984
                                                                    ; Pvar offset_17985
                                                                    ; Pvar DELTA_17986
                                                                    ; Pvar LEN_17987
                                                                    ; Pvar TRAIL_17988
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_17992 ]
                      ; cassgn (Lvar w_17991.(gv)) (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_17994)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_17993) ]) ] ]
          ; cassgn (Lvar AT_17990.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_17989) (Pvar AT32_17992)) ] ].

Definition fd_A2____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_ilen_read_upto32_at;
    f_params := args_A2____a_ilen_read_upto32_at;
    f_body := body_A2____a_ilen_read_upto32_at;
    f_tyout := tyout_A2____a_ilen_read_upto32_at;
    f_res := res_A2____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
