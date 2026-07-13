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

(* _poly_getnoise_eta2 *)
(* Local variables *)
Definition rp_8 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14126).
Definition seed_3 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 14127).
Definition nonce_0 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 14128).
Definition nonce_s : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 14129).
Definition buf_171 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14130).

(* Signature *)
Definition tyin__poly_getnoise_eta2 : seq atype :=
  [:: aarr U16 256; aarr U8 32; aword U8 ].
Definition args__poly_getnoise_eta2 : seq var_i :=
  [:: rp_8.(gv); seed_3.(gv); nonce_0.(gv) ].
Definition tyout__poly_getnoise_eta2 : seq atype := [:: aarr U16 256 ].
Definition res__poly_getnoise_eta2 : seq var_i := [:: rp_8.(gv) ].

(* Body *)
Definition body__poly_getnoise_eta2 : cmd :=
  [:: MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Spill [:: aarr U16 256%positive ])) [:: Pvar rp_8 ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U8 nonce_s.(gv) (Pconst (0)%Z)) AT_none (aword U8) (Pvar nonce_0))
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_171.(gv) ] _shake256_A128__A32_A1 [:: Pvar buf_171
                                                                    ; Pvar seed_3
                                                                    ; Pvar nonce_s ])
    ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aarr U16 256%positive ])) [:: Pvar rp_8 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar rp_8.(gv) ] __poly_cbd_eta1 [:: Pvar rp_8
                                                                    ; Pvar buf_171 ]) ].

Definition fd__poly_getnoise_eta2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__poly_getnoise_eta2;
    f_params := args__poly_getnoise_eta2;
    f_body := body__poly_getnoise_eta2;
    f_tyout := tyout__poly_getnoise_eta2;
    f_res := res__poly_getnoise_eta2;
    f_extra := tt;
  |}.

End IDO.
