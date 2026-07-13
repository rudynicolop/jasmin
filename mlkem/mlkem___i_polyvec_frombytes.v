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

(* __i_polyvec_frombytes *)
(* Local variables *)
Definition a_37 : gvar := mk_rocq_gvar Slocal (aarr U8 1152) (mkident 13935).
Definition r_15 : gvar := mk_rocq_gvar Slocal (aarr U16 768) (mkident 13936).
Definition i_92 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13937).

(* Signature *)
Definition tyin___i_polyvec_frombytes : seq atype := [:: aarr U8 1152 ].
Definition args___i_polyvec_frombytes : seq var_i := [:: a_37.(gv) ].
Definition tyout___i_polyvec_frombytes : seq atype := [:: aarr U16 768 ].
Definition res___i_polyvec_frombytes : seq var_i := [:: r_15.(gv) ].

(* Body *)
Definition body___i_polyvec_frombytes : cmd :=
  [:: MkI dummy_instr_info (Cfor
                              (i_92.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (3)%Z)
                              [:: MkI dummy_instr_info (Ccall [:: Lasub AAscale U16 256 r_15.(gv) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_92)) ] _i_poly_frombytes [:: Psub AAscale U16 256 r_15 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_92))
                                                                    ; Psub AAscale U8 384 a_37 (Papp2 (Omul (Op_int)) (Pconst (384)%Z) (Pvar i_92)) ]) ]) ].

Definition fd___i_polyvec_frombytes : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___i_polyvec_frombytes;
    f_params := args___i_polyvec_frombytes;
    f_body := body___i_polyvec_frombytes;
    f_tyout := tyout___i_polyvec_frombytes;
    f_res := res___i_polyvec_frombytes;
    f_extra := tt;
  |}.

End IDO.
