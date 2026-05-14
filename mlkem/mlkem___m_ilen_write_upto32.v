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

(* __m_ilen_write_upto32 *)
(* Local variables *)
Definition buf_18885 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18885).
Definition LEN_18886 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18886).
Definition w_18887 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18887).
Definition t128_18888 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18888).

(* Signature *)
Definition tyin___m_ilen_write_upto32 : seq atype :=
  [:: aword U64; aint; aword U256 ].
Definition args___m_ilen_write_upto32 : seq var_i :=
  [:: buf_18885.(gv); LEN_18886.(gv); w_18887.(gv) ].
Definition tyout___m_ilen_write_upto32 : seq atype := [:: aword U64; aint ].
Definition res___m_ilen_write_upto32 : seq var_i :=
  [:: buf_18885.(gv); LEN_18886.(gv) ].

(* Body *)
Definition body___m_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_18886))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_18886))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18885))) AT_none (aword U256) (Pvar w_18887))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_18885.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18885) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_18886.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18886) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_18888.(gv)) AT_none (aword U128) (Pvar w_18887))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_18886))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lmem Unaligned U128 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18885))) AT_none (aword U128) (Pvar t128_18888))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar buf_18885.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18885) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (16)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_18886.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18886) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_18888.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_18887
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_18885.(gv)
                                                                  ; Lvar LEN_18886.(gv) ] __m_ilen_write_upto16 [:: Pvar buf_18885
                                                                    ; Pvar LEN_18886
                                                                    ; Pvar t128_18888 ]) ]) ]
                              [::]) ].

Definition fd___m_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___m_ilen_write_upto32;
    f_params := args___m_ilen_write_upto32;
    f_body := body___m_ilen_write_upto32;
    f_tyout := tyout___m_ilen_write_upto32;
    f_res := res___m_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
