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

(* jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand *)
(* Local variables *)
Definition public_key : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 13605).
Definition secret_key : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2400) (mkident 13606).
Definition coins : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 13607).
Definition r_19 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13608).

(* Signature *)
Definition tyin_jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand : seq atype :=
  [:: aarr U8 1184; aarr U8 2400; aarr U8 64 ].
Definition args_jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand : seq var_i :=
  [:: public_key.(gv); secret_key.(gv); coins.(gv) ].
Definition tyout_jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand : seq atype :=
  [:: aarr U8 1184; aarr U8 2400; aword U64 ].
Definition res_jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand : seq var_i :=
  [:: public_key.(gv); secret_key.(gv); r_19.(gv) ].

(* Body *)
Definition body_jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (aword U64) ] AT_none (Oslh (SLHinit)) [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar public_key.(gv)
                                    ; Lvar secret_key.(gv) ] __crypto_kem_keypair_jazz [:: Pvar public_key
                                                                    ; Pvar secret_key
                                                                    ; Pvar coins ])
    ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lvar r_19.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U64)))) [::]) ].

Definition fd_jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand;
    f_params := args_jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand;
    f_body := body_jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand;
    f_tyout := tyout_jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand;
    f_res := res_jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand;
    f_extra := tt;
  |}.

End IDO.
