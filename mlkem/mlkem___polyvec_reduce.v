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

(* __polyvec_reduce *)
(* Local variables *)
Definition r_14 : gvar := mk_rocq_gvar Slocal (aarr U16 768) (mkident 13938).
Definition i_91 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13939).

(* Signature *)
Definition tyin___polyvec_reduce : seq atype := [:: aarr U16 768 ].
Definition args___polyvec_reduce : seq var_i := [:: r_14.(gv) ].
Definition tyout___polyvec_reduce : seq atype := [:: aarr U16 768 ].
Definition res___polyvec_reduce : seq var_i := [:: r_14.(gv) ].

(* Body *)
Definition body___polyvec_reduce : cmd :=
  [:: MkI dummy_instr_info (Cfor
                              (i_91.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (3)%Z)
                              [:: MkI dummy_instr_info (Ccall [:: Lasub AAscale U16 256 r_14.(gv) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_91)) ] __poly_reduce [:: Psub AAscale U16 256 r_14 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_91)) ]) ]) ].

Definition fd___polyvec_reduce : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___polyvec_reduce;
    f_params := args___polyvec_reduce;
    f_body := body___polyvec_reduce;
    f_tyout := tyout___polyvec_reduce;
    f_res := res___polyvec_reduce;
    f_extra := tt;
  |}.

End IDO.
