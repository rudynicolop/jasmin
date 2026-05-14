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
Definition shk_13615 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13615).
Definition ct_13616 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13616).
Definition sk_13617 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2400) (mkident 13617).
Definition z_13618 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13618).
Definition zp_ct : gvar := mk_rocq_gvar Slocal (aarr U8 1120) (mkident 13619).
Definition buf_13620 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 13620).
Definition k_13621 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13621).
Definition kr_13622 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 13622).
Definition ctc : gvar := mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13623).
Definition cnd_13624 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13624).
Definition j_13625 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13625).
Definition c_13626 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13626).

(* Signature *)
Definition tyin___crypto_kem_dec_jazz : seq atype :=
  [:: aarr U8 32; aarr U8 1088; aarr U8 2400 ].
Definition args___crypto_kem_dec_jazz : seq var_i :=
  [:: shk_13615.(gv); ct_13616.(gv); sk_13617.(gv) ].
Definition tyout___crypto_kem_dec_jazz : seq atype := [:: aarr U8 32 ].
Definition res___crypto_kem_dec_jazz : seq var_i := [:: shk_13615.(gv) ].

(* Body *)
Definition body___crypto_kem_dec_jazz : cmd :=
  [:: MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Spill [:: aarr U8 32%positive
                                                                    ; aarr U8 1088%positive ])) [:: Pvar shk_13615
                                                                    ; Pvar ct_13616 ])
    ; MkI dummy_instr_info (Cassgn (Lvar z_13618.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 sk_13617 (Papp2 (Osub (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Pconst (32)%Z))) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z))) (Pconst (32)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 zp_ct.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pvar z_13618))
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U8 32 buf_13620.(gv) (Pconst (0)%Z) ] __indcpa_dec [:: Psub AAscale U8 32 buf_13620 (Pconst (0)%Z)
                                                                    ; Pvar ct_13616
                                                                    ; Psub AAscale U8 1152 sk_13617 (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar k_13621.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 sk_13617 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Pconst (32)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 buf_13620.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Pvar k_13621))
    ; MkI dummy_instr_info (Ccall [:: Lvar kr_13622.(gv) ] _sha3_512A_A64 [:: Pvar kr_13622
                                                                    ; Pvar buf_13620 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar ctc.(gv) ] __indcpa_enc [:: Pvar ctc
                                                                    ; Psub AAscale U8 32 buf_13620 (Pconst (0)%Z)
                                                                    ; Psub AAscale U8 1184 sk_13617 (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z))
                                                                    ; Psub AAscale U8 32 kr_13622 (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U8 1088%positive ])) [:: Pvar ct_13616 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar cnd_13624.(gv) ] __verify [:: Pvar ct_13616
                                                                    ; Pvar ctc ])
    ; MkI dummy_instr_info (Cfor
                              (j_13625.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (320)%Z)) (Pconst (128)%Z)) (Pconst (32)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar c_13626.(gv)) AT_none (aword U256) (Pget Unaligned AAscale U256 ct_13616 (Pvar j_13625)))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 zp_ct.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pconst (32)%Z) (Pconst (32)%Z)) (Pvar j_13625))) AT_none (aword U256) (Pvar c_13626)) ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U8 32%positive ])) [:: Pvar shk_13615 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar shk_13615.(gv) ] _shake256_A32__A1120 [:: Pvar shk_13615
                                                                    ; Pvar zp_ct ])
    ; MkI dummy_instr_info (Ccall [:: Lvar shk_13615.(gv) ] __cmov [:: Pvar shk_13615
                                                                    ; Psub AAscale U8 32 kr_13622 (Pconst (0)%Z)
                                                                    ; Pvar cnd_13624 ]) ].

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
