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

(* __m_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18930).
Definition LEN_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18931).
Definition TRAIL_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18932).
Definition CUR_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18933).
Definition AT_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18934).
Definition w_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18935).
Definition AT32 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18936).
Definition t128_0_1 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18937).
Definition t128_1_1 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18938).

(* Signature *)
Definition tyin___m_ilen_read_upto32_at : seq atype :=
  [:: aword U64; aint; aint; aint; aint ].
Definition args___m_ilen_read_upto32_at : seq var_i :=
  [:: buf_1.(gv); LEN_1.(gv); TRAIL_1.(gv); CUR_1.(gv); AT_1.(gv) ].
Definition tyout___m_ilen_read_upto32_at : seq atype :=
  [:: aword U64; aint; aint; aint; aword U256 ].
Definition res___m_ilen_read_upto32_at : seq var_i :=
  [:: buf_1.(gv); LEN_1.(gv); TRAIL_1.(gv); AT_1.(gv); w_1.(gv) ].

(* Body *)
Definition body___m_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_1) (Pvar CUR_1)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_1) (Pconst (32)%Z)) (Pvar AT_1))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_1) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_1) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_1.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_1) (Pvar CUR_1)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_1)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_1.(gv)) AT_none (aword U256) (Pload Unaligned U256 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_1))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_1.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_1) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_1.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_1) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_1.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_1.(gv)
                                                                    ; Lvar LEN_1.(gv)
                                                                    ; Lvar TRAIL_1.(gv)
                                                                    ; Lvar AT32.(gv)
                                                                    ; Lvar t128_1_1.(gv) ] __m_ilen_read_upto16_at [:: Pvar buf_1
                                                                    ; Pvar LEN_1
                                                                    ; Pvar TRAIL_1
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_1.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_1
                                                                    ; Pvar t128_1_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_1.(gv)
                                                                    ; Lvar LEN_1.(gv)
                                                                    ; Lvar TRAIL_1.(gv)
                                                                    ; Lvar AT32.(gv)
                                                                    ; Lvar t128_0_1.(gv) ] __m_ilen_read_upto16_at [:: Pvar buf_1
                                                                    ; Pvar LEN_1
                                                                    ; Pvar TRAIL_1
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar buf_1.(gv)
                                                                    ; Lvar LEN_1.(gv)
                                                                    ; Lvar TRAIL_1.(gv)
                                                                    ; Lvar AT32.(gv)
                                                                    ; Lvar t128_1_1.(gv) ] __m_ilen_read_upto16_at [:: Pvar buf_1
                                                                    ; Pvar LEN_1
                                                                    ; Pvar TRAIL_1
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_1.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_1)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_1) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_1.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_1) (Pvar AT32))) ]) ].

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
