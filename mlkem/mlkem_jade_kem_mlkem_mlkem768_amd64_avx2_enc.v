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

(* jade_kem_mlkem_mlkem768_amd64_avx2_enc *)
(* Local variables *)
Definition ciphertext_13571 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13571).
Definition shared_secret_13572 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13572).
Definition public_key_13573 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 13573).
Definition r_13574 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13574).
Definition randomness_13575 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13575).
Definition randomnessp_13576 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13576).

(* Signature *)
Definition tyin_jade_kem_mlkem_mlkem768_amd64_avx2_enc : seq atype :=
  [:: aarr U8 1088; aarr U8 32; aarr U8 1184 ].
Definition args_jade_kem_mlkem_mlkem768_amd64_avx2_enc : seq var_i :=
  [:: ciphertext_13571.(gv)
    ; shared_secret_13572.(gv)
    ; public_key_13573.(gv) ].
Definition tyout_jade_kem_mlkem_mlkem768_amd64_avx2_enc : seq atype :=
  [:: aarr U8 1088; aarr U8 32; aword U64 ].
Definition res_jade_kem_mlkem_mlkem768_amd64_avx2_enc : seq var_i :=
  [:: ciphertext_13571.(gv); shared_secret_13572.(gv); r_13574.(gv) ].

(* Body *)
Definition body_jade_kem_mlkem_mlkem768_amd64_avx2_enc : cmd :=
  [:: copn [:: Lnone dummy_var_info (aword U64) ] (Oslh (SLHinit)) [::]
    ; cassgn (Lvar ciphertext_13571.(gv)) (aarr U8 1088) (Pvar ciphertext_13571)
    ; cassgn (Lvar shared_secret_13572.(gv)) (aarr U8 32) (Pvar shared_secret_13572)
    ; cassgn (Lvar public_key_13573.(gv)) (aarr U8 1184) (Pvar public_key_13573)
    ; cassgn (Lvar randomnessp_13576.(gv)) (aarr U8 32) (Pvar randomness_13575)
    ; crandombytes (Lvar randomnessp_13576.(gv)) U8 32%positive (Pvar randomnessp_13576)
    ; ccall [:: Lvar ciphertext_13571.(gv); Lvar shared_secret_13572.(gv) ] __crypto_kem_enc_jazz [:: Pvar ciphertext_13571
                                                                    ; Pvar shared_secret_13572
                                                                    ; Pvar public_key_13573
                                                                    ; Pvar randomnessp_13576 ]
    ; copn [:: Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lvar r_13574.(gv) ] (Oasm ((ExtOp (Oset0 U64)))) [::] ].

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
