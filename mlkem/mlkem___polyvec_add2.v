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

(* __polyvec_add2 *)
(* Local variables *)
Definition r_13946 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13946).
Definition b_13947 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13947).
Definition i_13948 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13948).

(* Signature *)
Definition tyin___polyvec_add2 : seq atype :=
  [:: aarr U16 768; aarr U16 768 ].
Definition args___polyvec_add2 : seq var_i :=
  [:: r_13946.(gv); b_13947.(gv) ].
Definition tyout___polyvec_add2 : seq atype := [:: aarr U16 768 ].
Definition res___polyvec_add2 : seq var_i := [:: r_13946.(gv) ].

(* Body *)
Definition body___polyvec_add2 : cmd :=
  [:: cfor
        (i_13948.(gv))
        (UpTo, Pconst (0)%Z, Pconst (3)%Z)
        [:: ccall [:: Lasub AAscale U16 256 r_13946.(gv) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_13948)) ] _poly_add2 [:: Psub AAscale U16 256 r_13946 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_13948))
                                                                    ; Psub AAscale U16 256 b_13947 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_13948)) ] ] ].

Definition fd___polyvec_add2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___polyvec_add2;
    f_params := args___polyvec_add2;
    f_body := body___polyvec_add2;
    f_tyout := tyout___polyvec_add2;
    f_res := res___polyvec_add2;
    f_extra := tt;
  |}.

End IDO.
