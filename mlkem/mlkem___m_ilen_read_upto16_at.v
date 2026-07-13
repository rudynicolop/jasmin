From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* __m_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18949).
Definition LEN_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18950).
Definition TRAIL_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18951).
Definition CUR_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18952).
Definition AT_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18953).
Definition w_0 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18954).
Definition AT16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18955).
Definition t64_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18956).
Definition t64_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18957).

(* Signature *)
Definition tyin___m_ilen_read_upto16_at : seq atype :=
  [:: aword U64; aint; aint; aint; aint ].
Definition args___m_ilen_read_upto16_at : seq var_i :=
  [:: buf_0.(gv); LEN_0.(gv); TRAIL_0.(gv); CUR_0.(gv); AT_0.(gv) ].
Definition tyout___m_ilen_read_upto16_at : seq atype :=
  [:: aword U64; aint; aint; aint; aword U128 ].
Definition res___m_ilen_read_upto16_at : seq var_i :=
  [:: buf_0.(gv); LEN_0.(gv); TRAIL_0.(gv); AT_0.(gv); w_0.(gv) ].

(* Body *)
Definition body___m_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_0) (Pvar CUR_0)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_0) (Pconst (16)%Z)) (Pvar AT_0))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_0) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_0) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_0.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_0) (Pvar CUR_0)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_0))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_0.(gv)) AT_none (aword U128) (Pload Unaligned U128 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_0))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_0.(gv) ] __SHLDQ [:: Pvar w_0
                                                                    ; Pvar AT16 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_0.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_0.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_0) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_0.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_0.(gv)
                                                                    ; Lvar LEN_0.(gv)
                                                                    ; Lvar TRAIL_0.(gv)
                                                                    ; Lvar AT16.(gv)
                                                                    ; Lvar t64_1.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf_0
                                                                    ; Pvar LEN_0
                                                                    ; Pvar TRAIL_0
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_0
                                                                    ; Pvar t64_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_0.(gv)
                                                                    ; Lvar LEN_0.(gv)
                                                                    ; Lvar TRAIL_0.(gv)
                                                                    ; Lvar AT16.(gv)
                                                                    ; Lvar t64_0.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf_0
                                                                    ; Pvar LEN_0
                                                                    ; Pvar TRAIL_0
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_0.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_0.(gv)
                                                                    ; Lvar LEN_0.(gv)
                                                                    ; Lvar TRAIL_0.(gv)
                                                                    ; Lvar AT16.(gv)
                                                                    ; Lvar t64_1.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf_0
                                                                    ; Pvar LEN_0
                                                                    ; Pvar TRAIL_0
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_0
                                                                    ; Pvar t64_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_0.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_0) (Pvar AT16))) ]) ].

Definition fd___m_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___m_ilen_read_upto16_at;
    f_params := args___m_ilen_read_upto16_at;
    f_body := body___m_ilen_read_upto16_at;
    f_tyout := tyout___m_ilen_read_upto16_at;
    f_res := res___m_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
