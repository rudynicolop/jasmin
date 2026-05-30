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

(* __polyvec_pointwise_acc *)
(* Local variables *)
Definition r_17 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13920).
Definition a_39 : gvar := mk_rocq_gvar Slocal (aarr U16 768) (mkident 13921).
Definition b_8 : gvar := mk_rocq_gvar Slocal (aarr U16 768) (mkident 13922).
Definition t_16 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13923).
Definition i_94 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13924).

(* Signature *)
Definition tyin___polyvec_pointwise_acc : seq atype :=
  [:: aarr U16 256; aarr U16 768; aarr U16 768 ].
Definition args___polyvec_pointwise_acc : seq var_i :=
  [:: r_17.(gv); a_39.(gv); b_8.(gv) ].
Definition tyout___polyvec_pointwise_acc : seq atype := [:: aarr U16 256 ].
Definition res___polyvec_pointwise_acc : seq var_i := [:: r_17.(gv) ].

(* Body *)
Definition body___polyvec_pointwise_acc : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar r_17.(gv) ] _poly_basemul [:: Pvar r_17
                                                                    ; Psub AAscale U16 256 a_39 (Pconst (0)%Z)
                                                                    ; Psub AAscale U16 256 b_8 (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cfor
                              (i_94.(gv))
                              (UpTo, Pconst (1)%Z, Pconst (3)%Z)
                              [:: MkI dummy_instr_info (Ccall [:: Lvar t_16.(gv) ] _poly_basemul [:: Pvar t_16
                                                                    ; Psub AAscale U16 256 a_39 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_94))
                                                                    ; Psub AAscale U16 256 b_8 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_94)) ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r_17.(gv) ] _poly_add2 [:: Pvar r_17
                                                                    ; Pvar t_16 ]) ]) ].

Definition fd___polyvec_pointwise_acc : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___polyvec_pointwise_acc;
    f_params := args___polyvec_pointwise_acc;
    f_body := body___polyvec_pointwise_acc;
    f_tyout := tyout___polyvec_pointwise_acc;
    f_res := res___polyvec_pointwise_acc;
    f_extra := tt;
  |}.

End IDO.
