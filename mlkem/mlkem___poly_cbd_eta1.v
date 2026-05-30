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

(* __poly_cbd_eta1 *)
(* Local variables *)
Definition rp_7 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14135).
Definition buf_170 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14136).

(* Signature *)
Definition tyin___poly_cbd_eta1 : seq atype :=
  [:: aarr U16 256; aarr U8 128 ].
Definition args___poly_cbd_eta1 : seq var_i := [:: rp_7.(gv); buf_170.(gv) ].
Definition tyout___poly_cbd_eta1 : seq atype := [:: aarr U16 256 ].
Definition res___poly_cbd_eta1 : seq var_i := [:: rp_7.(gv) ].

(* Body *)
Definition body___poly_cbd_eta1 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar rp_7.(gv) ] __cbd2 [:: Pvar rp_7
                                                                ; Psub AAscale U8 128 buf_170 (Pconst (0)%Z) ]) ].

Definition fd___poly_cbd_eta1 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___poly_cbd_eta1;
    f_params := args___poly_cbd_eta1;
    f_body := body___poly_cbd_eta1;
    f_tyout := tyout___poly_cbd_eta1;
    f_res := res___poly_cbd_eta1;
    f_extra := tt;
  |}.

End IDO.
