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

(* __polyvec_csubq *)
(* Local variables *)
Definition r_13944 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13944).
Definition i_13945 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13945).

(* Signature *)
Definition tyin___polyvec_csubq : seq atype := [:: aarr U16 768 ].
Definition args___polyvec_csubq : seq var_i := [:: r_13944.(gv) ].
Definition tyout___polyvec_csubq : seq atype := [:: aarr U16 768 ].
Definition res___polyvec_csubq : seq var_i := [:: r_13944.(gv) ].

(* Body *)
Definition body___polyvec_csubq : cmd :=
  [:: cfor
        (i_13945.(gv))
        (UpTo, Pconst (0)%Z, Pconst (3)%Z)
        [:: ccall [:: Lasub AAscale U16 256 r_13944.(gv) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_13945)) ] _poly_csubq [:: Psub AAscale U16 256 r_13944 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_13945)) ] ] ].

Definition fd___polyvec_csubq : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___polyvec_csubq;
    f_params := args___polyvec_csubq;
    f_body := body___polyvec_csubq;
    f_tyout := tyout___polyvec_csubq;
    f_res := res___polyvec_csubq;
    f_extra := tt;
  |}.

End IDO.
