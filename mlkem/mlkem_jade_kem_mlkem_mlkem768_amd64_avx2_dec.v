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

(* jade_kem_mlkem_mlkem768_amd64_avx2_dec *)
(* Local variables *)
Definition shared_secret_13562 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13562).
Definition ciphertext_13563 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13563).
Definition secret_key_13564 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2400) (mkident 13564).
Definition r_13565 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13565).

(* Signature *)
Definition tyin_jade_kem_mlkem_mlkem768_amd64_avx2_dec : seq atype :=
  [:: aarr U8 32; aarr U8 1088; aarr U8 2400 ].
Definition args_jade_kem_mlkem_mlkem768_amd64_avx2_dec : seq var_i :=
  [:: shared_secret_13562.(gv)
    ; ciphertext_13563.(gv)
    ; secret_key_13564.(gv) ].
Definition tyout_jade_kem_mlkem_mlkem768_amd64_avx2_dec : seq atype :=
  [:: aarr U8 32; aword U64 ].
Definition res_jade_kem_mlkem_mlkem768_amd64_avx2_dec : seq var_i :=
  [:: shared_secret_13562.(gv); r_13565.(gv) ].

(* Body *)
Definition body_jade_kem_mlkem_mlkem768_amd64_avx2_dec : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (aword U64) ] AT_none (Oslh (SLHinit)) [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar shared_secret_13562.(gv) ] __crypto_kem_dec_jazz [:: Pvar shared_secret_13562
                                                                    ; Pvar ciphertext_13563
                                                                    ; Pvar secret_key_13564 ])
    ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lvar r_13565.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U64)))) [::]) ].

Definition fd_jade_kem_mlkem_mlkem768_amd64_avx2_dec : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_jade_kem_mlkem_mlkem768_amd64_avx2_dec;
    f_params := args_jade_kem_mlkem_mlkem768_amd64_avx2_dec;
    f_body := body_jade_kem_mlkem_mlkem768_amd64_avx2_dec;
    f_tyout := tyout_jade_kem_mlkem_mlkem768_amd64_avx2_dec;
    f_res := res_jade_kem_mlkem_mlkem768_amd64_avx2_dec;
    f_extra := tt;
  |}.

End IDO.
