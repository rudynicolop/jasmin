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

(* __m_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_18911 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18911).
Definition LEN_18912 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18912).
Definition TRAIL_18913 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18913).
Definition CUR_18914 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18914).
Definition AT_18915 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18915).
Definition w256 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18916).
Definition AT8_18917 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18917).
Definition w_18918 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18918).
Definition t128 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18919).

(* Signature *)
Definition tyin___m_ilen_read_bcast_upto8_at : seq atype :=
  [:: aword U64; aint; aint; aint; aint ].
Definition args___m_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_18911.(gv)
    ; LEN_18912.(gv)
    ; TRAIL_18913.(gv)
    ; CUR_18914.(gv)
    ; AT_18915.(gv) ].
Definition tyout___m_ilen_read_bcast_upto8_at : seq atype :=
  [:: aword U64; aint; aint; aint; aword U256 ].
Definition res___m_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_18911.(gv)
    ; LEN_18912.(gv)
    ; TRAIL_18913.(gv)
    ; AT_18915.(gv)
    ; w256.(gv) ].

(* Body *)
Definition body___m_ilen_read_bcast_upto8_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_18915) (Pvar CUR_18914)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_18914) (Pconst (8)%Z)) (Pvar AT_18915))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_18912) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_18913) (Pconst (0)%Z))))
        [:: copn [:: Lvar w256.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_18912))
              [:: cassgn (Lvar AT8_18917.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_18915) (Pvar CUR_18914))
                ; copn [:: Lvar w256.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18911)) ]
                ; ccall [:: Lvar w256.(gv) ] __SHLQ_256 [:: Pvar w256
                                                          ; Pvar AT8_18917 ]
                ; cassgn (Lvar buf_18911.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18911) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18917))))
                ; cassgn (Lvar LEN_18912.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18912) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18917)))
                ; cassgn (Lvar AT_18915.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_18914) (Pconst (8)%Z)) ]
              [:: cassgn (Lvar AT8_18917.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_18915) (Pvar CUR_18914))
                ; ccall [:: Lvar buf_18911.(gv)
                          ; Lvar LEN_18912.(gv)
                          ; Lvar TRAIL_18913.(gv)
                          ; Lvar AT_18915.(gv)
                          ; Lvar w_18918.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf_18911
                                                                    ; Pvar LEN_18912
                                                                    ; Pvar TRAIL_18913
                                                                    ; Pvar CUR_18914
                                                                    ; Pvar AT_18915 ]
                ; cassgn (Lvar t128.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_18918))
                ; copn [:: Lvar w256.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128 ]
                ; ccall [:: Lvar w256.(gv) ] __SHLQ_256 [:: Pvar w256
                                                          ; Pvar AT8_18917 ] ] ] ].

Definition fd___m_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___m_ilen_read_bcast_upto8_at;
    f_params := args___m_ilen_read_bcast_upto8_at;
    f_body := body___m_ilen_read_bcast_upto8_at;
    f_tyout := tyout___m_ilen_read_bcast_upto8_at;
    f_res := res___m_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
