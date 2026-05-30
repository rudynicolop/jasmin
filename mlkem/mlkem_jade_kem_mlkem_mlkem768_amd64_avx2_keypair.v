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

(* jade_kem_mlkem_mlkem768_amd64_avx2_keypair *)
(* Local variables *)
Definition public_key_1 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 13583).
Definition secret_key_0 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2400) (mkident 13584).
Definition r_21 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13585).
Definition randomness : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 13586).
Definition randomnessp_2 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 13587).

(* Signature *)
Definition tyin_jade_kem_mlkem_mlkem768_amd64_avx2_keypair : seq atype :=
  [:: aarr U8 1184; aarr U8 2400 ].
Definition args_jade_kem_mlkem_mlkem768_amd64_avx2_keypair : seq var_i :=
  [:: public_key_1.(gv); secret_key_0.(gv) ].
Definition tyout_jade_kem_mlkem_mlkem768_amd64_avx2_keypair : seq atype :=
  [:: aarr U8 1184; aarr U8 2400; aword U64 ].
Definition res_jade_kem_mlkem_mlkem768_amd64_avx2_keypair : seq var_i :=
  [:: public_key_1.(gv); secret_key_0.(gv); r_21.(gv) ].

(* Body *)
Definition body_jade_kem_mlkem_mlkem768_amd64_avx2_keypair : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (aword U64) ] AT_none (Oslh (SLHinit)) [::])
    ; MkI dummy_instr_info (Cassgn (Lvar public_key_1.(gv)) AT_none (aarr U8 1184) (Pvar public_key_1))
    ; MkI dummy_instr_info (Cassgn (Lvar secret_key_0.(gv)) AT_none (aarr U8 2400) (Pvar secret_key_0))
    ; MkI dummy_instr_info (Cassgn (Lvar randomnessp_2.(gv)) AT_none (aarr U8 64) (Pvar randomness))
    ; MkI dummy_instr_info (Csyscall [:: (Lvar randomnessp_2.(gv))] (RandomBytes U8 64%positive) [:: (Pvar randomnessp_2)])
    ; MkI dummy_instr_info (Ccall [:: Lvar public_key_1.(gv)
                                    ; Lvar secret_key_0.(gv) ] __crypto_kem_keypair_jazz [:: Pvar public_key_1
                                                                    ; Pvar secret_key_0
                                                                    ; Pvar randomnessp_2 ])
    ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lvar r_21.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U64)))) [::]) ].

Definition fd_jade_kem_mlkem_mlkem768_amd64_avx2_keypair : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_jade_kem_mlkem_mlkem768_amd64_avx2_keypair;
    f_params := args_jade_kem_mlkem_mlkem768_amd64_avx2_keypair;
    f_body := body_jade_kem_mlkem_mlkem768_amd64_avx2_keypair;
    f_tyout := tyout_jade_kem_mlkem_mlkem768_amd64_avx2_keypair;
    f_res := res_jade_kem_mlkem_mlkem768_amd64_avx2_keypair;
    f_extra := tt;
  |}.

End IDO.
