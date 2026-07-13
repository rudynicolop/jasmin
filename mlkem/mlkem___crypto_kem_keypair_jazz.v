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

(* __crypto_kem_keypair_jazz *)
(* Local variables *)
Definition pk_1 : gvar := mk_rocq_gvar Slocal (aarr U8 1184) (mkident 13645).
Definition sk_1 : gvar := mk_rocq_gvar Slocal (aarr U8 2400) (mkident 13646).
Definition randomnessp_0 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 13647).
Definition s_randomnessp : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 13648).
Definition randomnessp1 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13649).
Definition skcpa : gvar := mk_rocq_gvar Slocal (aarr U8 1152) (mkident 13650).
Definition sk_s : gvar := mk_rocq_gvar Slocal (aarr U8 2400) (mkident 13651).
Definition i_100 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13652).
Definition t64_16 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13653).

(* Signature *)
Definition tyin___crypto_kem_keypair_jazz : seq atype :=
  [:: aarr U8 1184; aarr U8 2400; aarr U8 64 ].
Definition args___crypto_kem_keypair_jazz : seq var_i :=
  [:: pk_1.(gv); sk_1.(gv); randomnessp_0.(gv) ].
Definition tyout___crypto_kem_keypair_jazz : seq atype :=
  [:: aarr U8 1184; aarr U8 2400 ].
Definition res___crypto_kem_keypair_jazz : seq var_i :=
  [:: pk_1.(gv); sk_1.(gv) ].

(* Body *)
Definition body___crypto_kem_keypair_jazz : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar s_randomnessp.(gv)) AT_none (aarr U8 64) (Pvar randomnessp_0))
    ; MkI dummy_instr_info (Cassgn (Lvar randomnessp1.(gv)) AT_none (aarr U8 32) (Psub AAscale U8 32 randomnessp_0 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar skcpa.(gv)) AT_none (aarr U8 1152) (Psub AAscale U8 1152 sk_1 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar sk_s.(gv)) AT_none (aarr U8 2400) (Pvar sk_1))
    ; MkI dummy_instr_info (Ccall [:: Lvar pk_1.(gv); Lvar skcpa.(gv) ] __indcpa_keypair [:: Pvar pk_1
                                                                    ; Pvar skcpa
                                                                    ; Pvar randomnessp1 ])
    ; MkI dummy_instr_info (Cassgn (Lvar sk_1.(gv)) AT_none (aarr U8 2400) (Pvar sk_s))
    ; MkI dummy_instr_info (Cassgn (Lasub AAscale U8 1152 sk_1.(gv) (Pconst (0)%Z)) AT_none (aarr U8 1152) (Pvar skcpa))
    ; MkI dummy_instr_info (Cfor
                              (i_100.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Pconst (32)%Z)) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t64_16.(gv)) AT_none (aword U64) (Pget Unaligned AAscale U64 pk_1 (Pvar i_100)))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 sk_1.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Pconst (8)%Z)) (Pvar i_100)) (Pconst (8)%Z))) AT_none (aword U64) (Pvar t64_16)) ])
    ; MkI dummy_instr_info (Ccall [:: Lasub AAscale U8 32 sk_1.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Pconst (32)%Z))) ] _sha3_256A_A1184 [:: Psub AAscale U8 32 sk_1 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Pconst (32)%Z)))
                                                                    ; Pvar pk_1 ])
    ; MkI dummy_instr_info (Cassgn (Lvar randomnessp_0.(gv)) AT_none (aarr U8 64) (Pvar s_randomnessp))
    ; MkI dummy_instr_info (Cfor
                              (i_100.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t64_16.(gv)) AT_none (aword U64) (Pget Unaligned AAscale U64 randomnessp_0 (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z)) (Pvar i_100))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 sk_1.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (384)%Z)) (Pconst (32)%Z))) (Pconst (32)%Z)) (Pconst (8)%Z)) (Pvar i_100)) (Pconst (8)%Z))) AT_none (aword U64) (Pvar t64_16)) ]) ].

Definition fd___crypto_kem_keypair_jazz : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___crypto_kem_keypair_jazz;
    f_params := args___crypto_kem_keypair_jazz;
    f_body := body___crypto_kem_keypair_jazz;
    f_tyout := tyout___crypto_kem_keypair_jazz;
    f_res := res___crypto_kem_keypair_jazz;
    f_extra := tt;
  |}.

End IDO.
