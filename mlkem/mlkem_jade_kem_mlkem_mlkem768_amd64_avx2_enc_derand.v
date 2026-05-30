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

(* jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand *)
(* Local variables *)
Definition ciphertext : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13593).
Definition shared_secret : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13594).
Definition public_key_0 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 13595).
Definition coins_0 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13596).
Definition r_20 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13597).

(* Signature *)
Definition tyin_jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand : seq atype :=
  [:: aarr U8 1088; aarr U8 32; aarr U8 1184; aarr U8 32 ].
Definition args_jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand : seq var_i :=
  [:: ciphertext.(gv); shared_secret.(gv); public_key_0.(gv); coins_0.(gv) ].
Definition tyout_jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand : seq atype :=
  [:: aarr U8 1088; aarr U8 32; aword U64 ].
Definition res_jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand : seq var_i :=
  [:: ciphertext.(gv); shared_secret.(gv); r_20.(gv) ].

(* Body *)
Definition body_jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (aword U64) ] AT_none (Oslh (SLHinit)) [::])
    ; MkI dummy_instr_info (Cassgn (Lvar public_key_0.(gv)) AT_none (aarr U8 1184) (Pvar public_key_0))
    ; MkI dummy_instr_info (Ccall [:: Lvar ciphertext.(gv)
                                    ; Lvar shared_secret.(gv) ] __crypto_kem_enc_jazz [:: Pvar ciphertext
                                                                    ; Pvar shared_secret
                                                                    ; Pvar public_key_0
                                                                    ; Pvar coins_0 ])
    ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lvar r_20.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U64)))) [::]) ].

Definition fd_jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand;
    f_params := args_jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand;
    f_body := body_jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand;
    f_tyout := tyout_jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand;
    f_res := res_jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand;
    f_extra := tt;
  |}.

End IDO.
