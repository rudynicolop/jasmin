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

(* jade_kem_mlkem_mlkem768_amd64_avx2_enc *)
(* Local variables *)
Definition ciphertext_0 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13571).
Definition shared_secret_0 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13572).
Definition public_key_2 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 13573).
Definition r_22 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13574).
Definition randomness_0 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13575).
Definition randomnessp_3 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13576).

(* Signature *)
Definition tyin_jade_kem_mlkem_mlkem768_amd64_avx2_enc : seq atype :=
  [:: aarr U8 1088; aarr U8 32; aarr U8 1184 ].
Definition args_jade_kem_mlkem_mlkem768_amd64_avx2_enc : seq var_i :=
  [:: ciphertext_0.(gv); shared_secret_0.(gv); public_key_2.(gv) ].
Definition tyout_jade_kem_mlkem_mlkem768_amd64_avx2_enc : seq atype :=
  [:: aarr U8 1088; aarr U8 32; aword U64 ].
Definition res_jade_kem_mlkem_mlkem768_amd64_avx2_enc : seq var_i :=
  [:: ciphertext_0.(gv); shared_secret_0.(gv); r_22.(gv) ].

(* Body *)
Definition body_jade_kem_mlkem_mlkem768_amd64_avx2_enc : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (aword U64) ] AT_none (Oslh (SLHinit)) [::])
    ; MkI dummy_instr_info (Cassgn (Lvar ciphertext_0.(gv)) AT_none (aarr U8 1088) (Pvar ciphertext_0))
    ; MkI dummy_instr_info (Cassgn (Lvar shared_secret_0.(gv)) AT_none (aarr U8 32) (Pvar shared_secret_0))
    ; MkI dummy_instr_info (Cassgn (Lvar public_key_2.(gv)) AT_none (aarr U8 1184) (Pvar public_key_2))
    ; MkI dummy_instr_info (Cassgn (Lvar randomnessp_3.(gv)) AT_none (aarr U8 32) (Pvar randomness_0))
    ; MkI dummy_instr_info (Csyscall [:: (Lvar randomnessp_3.(gv))] (RandomBytes U8 32%positive) [:: (Pvar randomnessp_3)])
    ; MkI dummy_instr_info (Ccall [:: Lvar ciphertext_0.(gv)
                                    ; Lvar shared_secret_0.(gv) ] __crypto_kem_enc_jazz [:: Pvar ciphertext_0
                                                                    ; Pvar shared_secret_0
                                                                    ; Pvar public_key_2
                                                                    ; Pvar randomnessp_3 ])
    ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lvar r_22.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U64)))) [::]) ].

Definition fd_jade_kem_mlkem_mlkem768_amd64_avx2_enc : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_jade_kem_mlkem_mlkem768_amd64_avx2_enc;
    f_params := args_jade_kem_mlkem_mlkem768_amd64_avx2_enc;
    f_body := body_jade_kem_mlkem_mlkem768_amd64_avx2_enc;
    f_tyout := tyout_jade_kem_mlkem_mlkem768_amd64_avx2_enc;
    f_res := res_jade_kem_mlkem_mlkem768_amd64_avx2_enc;
    f_extra := tt;
  |}.

End IDO.
