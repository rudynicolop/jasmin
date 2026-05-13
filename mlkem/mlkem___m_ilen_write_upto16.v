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

(* __m_ilen_write_upto16 *)
(* Local variables *)
Definition buf_18894 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18894).
Definition LEN_18895 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18895).
Definition w_18896 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18896).
Definition t64 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18897).

(* Signature *)
Definition tyin___m_ilen_write_upto16 : seq atype :=
  [:: aword U64; aint; aword U128 ].
Definition args___m_ilen_write_upto16 : seq var_i :=
  [:: buf_18894.(gv); LEN_18895.(gv); w_18896.(gv) ].
Definition tyout___m_ilen_write_upto16 : seq atype := [:: aword U64; aint ].
Definition res___m_ilen_write_upto16 : seq var_i :=
  [:: buf_18894.(gv); LEN_18895.(gv) ].

(* Body *)
Definition body___m_ilen_write_upto16 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_18895))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_18895))
              [:: cassgn (Lmem Unaligned U128 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18894))) (aword U128) (Pvar w_18896)
                ; cassgn (Lvar buf_18894.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18894) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (16)%Z)))
                ; cassgn (Lvar LEN_18895.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18895) (Pconst (16)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_18895))
                    [:: copn [:: Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18894)) ] (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_18896 ]
                      ; cassgn (Lvar buf_18894.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18894) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
                      ; cassgn (Lvar LEN_18895.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18895) (Pconst (8)%Z))
                      ; copn [:: Lvar w_18896.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_18896
                                                                    ; Pvar w_18896 ] ]
                    [::]
                ; cassgn (Lvar t64.(gv)) (aword U64) (Pvar w_18896)
                ; ccall [:: Lvar buf_18894.(gv); Lvar LEN_18895.(gv) ] __m_ilen_write_upto8 [:: Pvar buf_18894
                                                                    ; Pvar LEN_18895
                                                                    ; Pvar t64 ] ] ]
        [::] ].

Definition fd___m_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___m_ilen_write_upto16;
    f_params := args___m_ilen_write_upto16;
    f_body := body___m_ilen_write_upto16;
    f_tyout := tyout___m_ilen_write_upto16;
    f_res := res___m_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
