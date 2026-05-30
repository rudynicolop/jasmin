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

(* __polyvec_invntt *)
(* Local variables *)
Definition r_12 : gvar := mk_rocq_gvar Slocal (aarr U16 768) (mkident 13942).
Definition i_89 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13943).

(* Signature *)
Definition tyin___polyvec_invntt : seq atype := [:: aarr U16 768 ].
Definition args___polyvec_invntt : seq var_i := [:: r_12.(gv) ].
Definition tyout___polyvec_invntt : seq atype := [:: aarr U16 768 ].
Definition res___polyvec_invntt : seq var_i := [:: r_12.(gv) ].

(* Body *)
Definition body___polyvec_invntt : cmd :=
  [:: MkI dummy_instr_info (Cfor
                              (i_89.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (3)%Z)
                              [:: MkI dummy_instr_info (Ccall [:: Lasub AAscale U16 256 r_12.(gv) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_89)) ] _poly_invntt [:: Psub AAscale U16 256 r_12 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_89)) ]) ]) ].

Definition fd___polyvec_invntt : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___polyvec_invntt;
    f_params := args___polyvec_invntt;
    f_body := body___polyvec_invntt;
    f_tyout := tyout___polyvec_invntt;
    f_res := res___polyvec_invntt;
    f_extra := tt;
  |}.

End IDO.
