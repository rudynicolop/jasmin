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

(* __crypto_kem_enc_jazz *)
(* Local variables *)
Definition ct_13631 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13631).
Definition shk : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13632).
Definition pk_13633 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 13633).
Definition randomnessp_13634 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13634).
Definition b_13635 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13635).
Definition buf_13636 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 13636).
Definition kr : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 13637).
Definition k_13638 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13638).

(* Signature *)
Definition tyin___crypto_kem_enc_jazz : seq atype :=
  [:: aarr U8 1088; aarr U8 32; aarr U8 1184; aarr U8 32 ].
Definition args___crypto_kem_enc_jazz : seq var_i :=
  [:: ct_13631.(gv); shk.(gv); pk_13633.(gv); randomnessp_13634.(gv) ].
Definition tyout___crypto_kem_enc_jazz : seq atype :=
  [:: aarr U8 1088; aarr U8 32 ].
Definition res___crypto_kem_enc_jazz : seq var_i :=
  [:: ct_13631.(gv); shk.(gv) ].

(* Body *)
Definition body___crypto_kem_enc_jazz : cmd :=
  [:: MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Spill [:: aarr U8 1184%positive
                                                                    ; aarr U8 32%positive ])) [:: Pvar pk_13633
                                                                    ; Pvar shk ])
    ; MkI dummy_instr_info (Cassgn (Lvar b_13635.(gv)) AT_none (aword U256) (Pget Unaligned AAscale U256 randomnessp_13634 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 buf_13636.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pvar b_13635))
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U8 32 buf_13636.(gv) (Pconst (32)%Z) ] _sha3_256A_A1184 [:: Psub AAscale U8 32 buf_13636 (Pconst (32)%Z)
                                                                    ; Pvar pk_13633 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar kr.(gv) ] _sha3_512A_A64 [:: Pvar kr
                                                                    ; Pvar buf_13636 ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U8 1184%positive ])) [:: Pvar pk_13633 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar ct_13631.(gv) ] __indcpa_enc [:: Pvar ct_13631
                                                                    ; Psub AAscale U8 32 buf_13636 (Pconst (0)%Z)
                                                                    ; Pvar pk_13633
                                                                    ; Psub AAscale U8 32 kr (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U8 32%positive ])) [:: Pvar shk ])
    ; MkI dummy_instr_info (Cassgn (Lvar k_13638.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 kr (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAscale U256 shk.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pvar k_13638)) ].

Definition fd___crypto_kem_enc_jazz : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___crypto_kem_enc_jazz;
    f_params := args___crypto_kem_enc_jazz;
    f_body := body___crypto_kem_enc_jazz;
    f_tyout := tyout___crypto_kem_enc_jazz;
    f_res := res___crypto_kem_enc_jazz;
    f_extra := tt;
  |}.

End IDO.
