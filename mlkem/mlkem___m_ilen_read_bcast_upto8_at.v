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

(* __m_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18911).
Definition LEN_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18912).
Definition TRAIL_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18913).
Definition CUR_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18914).
Definition AT_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18915).
Definition w256 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18916).
Definition AT8_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18917).
Definition w_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18918).
Definition t128 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18919).

(* Signature *)
Definition tyin___m_ilen_read_bcast_upto8_at : seq atype :=
  [:: aword U64; aint; aint; aint; aint ].
Definition args___m_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_2.(gv); LEN_2.(gv); TRAIL_2.(gv); CUR_2.(gv); AT_2.(gv) ].
Definition tyout___m_ilen_read_bcast_upto8_at : seq atype :=
  [:: aword U64; aint; aint; aint; aword U256 ].
Definition res___m_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_2.(gv); LEN_2.(gv); TRAIL_2.(gv); AT_2.(gv); w256.(gv) ].

(* Body *)
Definition body___m_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_2) (Pvar CUR_2)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_2) (Pconst (8)%Z)) (Pvar AT_2))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_2) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_2) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_2))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_0.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_2) (Pvar CUR_2)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_2)) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256.(gv) ] __SHLQ_256 [:: Pvar w256
                                                                    ; Pvar AT8_0 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_2.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_0)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_2.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_2) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_0))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_2.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_2) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_0.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_2) (Pvar CUR_2)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_2.(gv)
                                                                  ; Lvar LEN_2.(gv)
                                                                  ; Lvar TRAIL_2.(gv)
                                                                  ; Lvar AT_2.(gv)
                                                                  ; Lvar w_2.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf_2
                                                                    ; Pvar LEN_2
                                                                    ; Pvar TRAIL_2
                                                                    ; Pvar CUR_2
                                                                    ; Pvar AT_2 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_2)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256.(gv) ] __SHLQ_256 [:: Pvar w256
                                                                    ; Pvar AT8_0 ]) ]) ]) ].

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
