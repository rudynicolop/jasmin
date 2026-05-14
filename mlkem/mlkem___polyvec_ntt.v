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

(* __polyvec_ntt *)
(* Local variables *)
Definition r_13940 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13940).
Definition i_13941 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13941).

(* Signature *)
Definition tyin___polyvec_ntt : seq atype := [:: aarr U16 768 ].
Definition args___polyvec_ntt : seq var_i := [:: r_13940.(gv) ].
Definition tyout___polyvec_ntt : seq atype := [:: aarr U16 768 ].
Definition res___polyvec_ntt : seq var_i := [:: r_13940.(gv) ].

(* Body *)
Definition body___polyvec_ntt : cmd :=
  [:: MkI dummy_instr_info (Cfor
                              (i_13941.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (3)%Z)
                              [:: MkI dummy_instr_info (Ccall [:: Lasub AAscale U16 256 r_13940.(gv) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_13941)) ] _poly_ntt [:: Psub AAscale U16 256 r_13940 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_13941)) ]) ]) ].

Definition fd___polyvec_ntt : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___polyvec_ntt;
    f_params := args___polyvec_ntt;
    f_body := body___polyvec_ntt;
    f_tyout := tyout___polyvec_ntt;
    f_res := res___polyvec_ntt;
    f_extra := tt;
  |}.

End IDO.
