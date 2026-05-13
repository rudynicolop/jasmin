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

(* _poly_getnoise_eta2 *)
(* Local variables *)
Definition rp_14126 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14126).
Definition seed_14127 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 14127).
Definition nonce_14128 : gvar :=
  mk_rocq_gvar Slocal (aword U8) (mkident 14128).
Definition nonce_s : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 14129).
Definition buf_14130 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14130).

(* Signature *)
Definition tyin__poly_getnoise_eta2 : seq atype :=
  [:: aarr U16 256; aarr U8 32; aword U8 ].
Definition args__poly_getnoise_eta2 : seq var_i :=
  [:: rp_14126.(gv); seed_14127.(gv); nonce_14128.(gv) ].
Definition tyout__poly_getnoise_eta2 : seq atype := [:: aarr U16 256 ].
Definition res__poly_getnoise_eta2 : seq var_i := [:: rp_14126.(gv) ].

(* Body *)
Definition body__poly_getnoise_eta2 : cmd :=
  [:: copn [::] (Opseudo_op (Ospill Spill [:: aarr U16 256%positive ])) [:: Pvar rp_14126 ]
    ; cassgn (Laset Aligned AAscale U8 nonce_s.(gv) (Pconst (0)%Z)) (aword U8) (Pvar nonce_14128)
    ; ccall [:: Lvar buf_14130.(gv) ] _shake256_A128__A32_A1 [:: Pvar buf_14130
                                                               ; Pvar seed_14127
                                                               ; Pvar nonce_s ]
    ; copn [::] (Opseudo_op (Ospill Unspill [:: aarr U16 256%positive ])) [:: Pvar rp_14126 ]
    ; ccall [:: Lvar rp_14126.(gv) ] __poly_cbd_eta1 [:: Pvar rp_14126
                                                       ; Pvar buf_14130 ] ].

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
