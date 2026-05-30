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
Definition ct_2 : gvar := mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13631).
Definition shk : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13632).
Definition pk_2 : gvar := mk_rocq_gvar Slocal (aarr U8 1184) (mkident 13633).
Definition randomnessp_1 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13634).
Definition b_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13635).
Definition buf_180 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 13636).
Definition kr : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 13637).
Definition k_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13638).

(* Signature *)
Definition tyin___crypto_kem_enc_jazz : seq atype :=
  [:: aarr U8 1088; aarr U8 32; aarr U8 1184; aarr U8 32 ].
Definition args___crypto_kem_enc_jazz : seq var_i :=
  [:: ct_2.(gv); shk.(gv); pk_2.(gv); randomnessp_1.(gv) ].
Definition tyout___crypto_kem_enc_jazz : seq atype :=
  [:: aarr U8 1088; aarr U8 32 ].
Definition res___crypto_kem_enc_jazz : seq var_i := [:: ct_2.(gv); shk.(gv) ].

(* Body *)
Definition body___crypto_kem_enc_jazz : cmd :=
  [:: MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Spill [:: aarr U8 1184%positive
                                                                    ; aarr U8 32%positive ])) [:: Pvar pk_2
                                                                    ; Pvar shk ])
    ; MkI dummy_instr_info (Cassgn (Lvar b_10.(gv)) AT_none (aword U256) (Pget Unaligned AAscale U256 randomnessp_1 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 buf_180.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pvar b_10))
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U8 32 buf_180.(gv) (Pconst (32)%Z) ] _sha3_256A_A1184 [:: Psub AAscale U8 32 buf_180 (Pconst (32)%Z)
                                                                    ; Pvar pk_2 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar kr.(gv) ] _sha3_512A_A64 [:: Pvar kr
                                                                    ; Pvar buf_180 ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U8 1184%positive ])) [:: Pvar pk_2 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar ct_2.(gv) ] __indcpa_enc [:: Pvar ct_2
                                                                    ; Psub AAscale U8 32 buf_180 (Pconst (0)%Z)
                                                                    ; Pvar pk_2
                                                                    ; Psub AAscale U8 32 kr (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U8 32%positive ])) [:: Pvar shk ])
    ; MkI dummy_instr_info (Cassgn (Lvar k_1.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 kr (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAscale U256 shk.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pvar k_1)) ].

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
