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

(* __m_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_18930 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18930).
Definition LEN_18931 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18931).
Definition TRAIL_18932 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18932).
Definition CUR_18933 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18933).
Definition AT_18934 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18934).
Definition w_18935 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18935).
Definition AT32 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18936).
Definition t128_0_18937 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18937).
Definition t128_1_18938 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18938).

(* Signature *)
Definition tyin___m_ilen_read_upto32_at : seq atype :=
  [:: aword U64; aint; aint; aint; aint ].
Definition args___m_ilen_read_upto32_at : seq var_i :=
  [:: buf_18930.(gv)
    ; LEN_18931.(gv)
    ; TRAIL_18932.(gv)
    ; CUR_18933.(gv)
    ; AT_18934.(gv) ].
Definition tyout___m_ilen_read_upto32_at : seq atype :=
  [:: aword U64; aint; aint; aint; aword U256 ].
Definition res___m_ilen_read_upto32_at : seq var_i :=
  [:: buf_18930.(gv)
    ; LEN_18931.(gv)
    ; TRAIL_18932.(gv)
    ; AT_18934.(gv)
    ; w_18935.(gv) ].

(* Body *)
Definition body___m_ilen_read_upto32_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_18934) (Pvar CUR_18933)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_18933) (Pconst (32)%Z)) (Pvar AT_18934))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_18931) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_18932) (Pconst (0)%Z))))
        [:: copn [:: Lvar w_18935.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cassgn (Lvar AT32.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_18934) (Pvar CUR_18933))
          ; cif
              (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_18931)))
              [:: cassgn (Lvar w_18935.(gv)) (aword U256) (Pload Unaligned U256 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18930)))
                ; cassgn (Lvar AT32.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32) (Pconst (32)%Z))
                ; cassgn (Lvar buf_18930.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18930) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
                ; cassgn (Lvar LEN_18931.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18931) (Pconst (32)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32))
                    [:: copn [:: Lvar w_18935.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::]
                      ; ccall [:: Lvar buf_18930.(gv)
                                ; Lvar LEN_18931.(gv)
                                ; Lvar TRAIL_18932.(gv)
                                ; Lvar AT32.(gv)
                                ; Lvar t128_1_18938.(gv) ] __m_ilen_read_upto16_at [:: Pvar buf_18930
                                                                    ; Pvar LEN_18931
                                                                    ; Pvar TRAIL_18932
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32 ]
                      ; copn [:: Lvar w_18935.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_18935
                                                                    ; Pvar t128_1_18938
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [:: ccall [:: Lvar buf_18930.(gv)
                                ; Lvar LEN_18931.(gv)
                                ; Lvar TRAIL_18932.(gv)
                                ; Lvar AT32.(gv)
                                ; Lvar t128_0_18937.(gv) ] __m_ilen_read_upto16_at [:: Pvar buf_18930
                                                                    ; Pvar LEN_18931
                                                                    ; Pvar TRAIL_18932
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32 ]
                      ; ccall [:: Lvar buf_18930.(gv)
                                ; Lvar LEN_18931.(gv)
                                ; Lvar TRAIL_18932.(gv)
                                ; Lvar AT32.(gv)
                                ; Lvar t128_1_18938.(gv) ] __m_ilen_read_upto16_at [:: Pvar buf_18930
                                                                    ; Pvar LEN_18931
                                                                    ; Pvar TRAIL_18932
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32 ]
                      ; cassgn (Lvar w_18935.(gv)) (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_18938)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_18937) ]) ] ]
          ; cassgn (Lvar AT_18934.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_18933) (Pvar AT32)) ] ].

Definition fd___m_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___m_ilen_read_upto32_at;
    f_params := args___m_ilen_read_upto32_at;
    f_body := body___m_ilen_read_upto32_at;
    f_tyout := tyout___m_ilen_read_upto32_at;
    f_res := res___m_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
