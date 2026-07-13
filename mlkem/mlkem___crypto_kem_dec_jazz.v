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

(* __crypto_kem_dec_jazz *)
(* Local variables *)
Definition shk_0 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13615).
Definition ct_3 : gvar := mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13616).
Definition sk_2 : gvar := mk_rocq_gvar Slocal (aarr U8 2400) (mkident 13617).
Definition z_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13618).
Definition zp_ct : gvar := mk_rocq_gvar Slocal (aarr U8 1120) (mkident 13619).
Definition buf_181 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 13620).
Definition k_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13621).
Definition kr_0 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 13622).
Definition ctc : gvar := mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13623).
Definition cnd_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13624).
Definition j_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13625).
Definition c_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13626).

(* Signature *)
Definition tyin___crypto_kem_dec_jazz : seq atype :=
  [:: aarr U8 32; aarr U8 1088; aarr U8 2400 ].
Definition args___crypto_kem_dec_jazz : seq var_i :=
  [:: shk_0.(gv); ct_3.(gv); sk_2.(gv) ].
Definition tyout___crypto_kem_dec_jazz : seq atype := [:: aarr U8 32 ].
Definition res___crypto_kem_dec_jazz : seq var_i := [:: shk_0.(gv) ].

(* Body *)
Definition body___crypto_kem_dec_jazz : cmd :=
  [:: MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Spill [:: aarr U8 32%positive
                                                                    ; aarr U8 1088%positive ])) [:: Pvar shk_0
                                                                    ; Pvar ct_3 ])
    ; MkI dummy_instr_info (Cassgn (Lvar z_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 sk_2 (Papp2 (Osub (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Pconst (32)%Z))) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z))) (Pconst (32)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 zp_ct.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pvar z_0))
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U8 32 buf_181.(gv) (Pconst (0)%Z) ] __indcpa_dec [:: Psub AAscale U8 32 buf_181 (Pconst (0)%Z)
                                                                    ; Pvar ct_3
                                                                    ; Psub AAscale U8 1152 sk_2 (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar k_2.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 sk_2 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Pconst (32)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 buf_181.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Pvar k_2))
    ; MkI dummy_instr_info (Ccall [:: Lvar kr_0.(gv) ] _sha3_512A_A64 [:: Pvar kr_0
                                                                    ; Pvar buf_181 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar ctc.(gv) ] __indcpa_enc [:: Pvar ctc
                                                                    ; Psub AAscale U8 32 buf_181 (Pconst (0)%Z)
                                                                    ; Psub AAscale U8 1184 sk_2 (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z))
                                                                    ; Psub AAscale U8 32 kr_0 (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U8 1088%positive ])) [:: Pvar ct_3 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar cnd_1.(gv) ] __verify [:: Pvar ct_3
                                                                   ; Pvar ctc ])
    ; MkI dummy_instr_info (Cfor
                              (j_0.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (320)%Z)) (Pconst (128)%Z)) (Pconst (32)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar c_1.(gv)) AT_none (aword U256) (Pget Unaligned AAscale U256 ct_3 (Pvar j_0)))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 zp_ct.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pconst (32)%Z) (Pconst (32)%Z)) (Pvar j_0))) AT_none (aword U256) (Pvar c_1)) ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U8 32%positive ])) [:: Pvar shk_0 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar shk_0.(gv) ] _shake256_A32__A1120 [:: Pvar shk_0
                                                                    ; Pvar zp_ct ])
    ; MkI dummy_instr_info (Ccall [:: Lvar shk_0.(gv) ] __cmov [:: Pvar shk_0
                                                                 ; Psub AAscale U8 32 kr_0 (Pconst (0)%Z)
                                                                 ; Pvar cnd_1 ]) ].

Definition fd___crypto_kem_dec_jazz : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___crypto_kem_dec_jazz;
    f_params := args___crypto_kem_dec_jazz;
    f_body := body___crypto_kem_dec_jazz;
    f_tyout := tyout___crypto_kem_dec_jazz;
    f_res := res___crypto_kem_dec_jazz;
    f_extra := tt;
  |}.

End IDO.
