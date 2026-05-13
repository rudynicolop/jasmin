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

(* __i_polyvec_tobytes *)
(* Local variables *)
Definition r_13929 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1152) (mkident 13929).
Definition a_13930 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13930).
Definition i_13931 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13931).

(* Signature *)
Definition tyin___i_polyvec_tobytes : seq atype :=
  [:: aarr U8 1152; aarr U16 768 ].
Definition args___i_polyvec_tobytes : seq var_i :=
  [:: r_13929.(gv); a_13930.(gv) ].
Definition tyout___i_polyvec_tobytes : seq atype := [:: aarr U8 1152 ].
Definition res___i_polyvec_tobytes : seq var_i := [:: r_13929.(gv) ].

(* Body *)
Definition body___i_polyvec_tobytes : cmd :=
  [:: cfor
        (i_13931.(gv))
        (UpTo, Pconst (0)%Z, Pconst (3)%Z)
        [:: ccall [:: Lasub AAscale U8 384 r_13929.(gv) (Papp2 (Omul (Op_int)) (Pconst (384)%Z) (Pvar i_13931))
                    ; Lasub AAscale U16 256 a_13930.(gv) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_13931)) ] _i_poly_tobytes [:: Psub AAscale U8 384 r_13929 (Papp2 (Omul (Op_int)) (Pconst (384)%Z) (Pvar i_13931))
                                                                    ; Psub AAscale U16 256 a_13930 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_13931)) ] ] ].

Definition fd___i_polyvec_tobytes : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___i_polyvec_tobytes;
    f_params := args___i_polyvec_tobytes;
    f_body := body___i_polyvec_tobytes;
    f_tyout := tyout___i_polyvec_tobytes;
    f_res := res___i_polyvec_tobytes;
    f_extra := tt;
  |}.

End IDO.
