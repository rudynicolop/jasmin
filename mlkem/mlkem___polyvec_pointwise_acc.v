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
Definition r_13920 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13920).
Definition a_13921 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13921).
Definition b_13922 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13922).
Definition t_13923 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13923).
Definition i_13924 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13924).

(* Signature *)
Definition tyin___polyvec_pointwise_acc : seq atype :=
  [:: aarr U16 256; aarr U16 768; aarr U16 768 ].
Definition args___polyvec_pointwise_acc : seq var_i :=
  [:: r_13920.(gv); a_13921.(gv); b_13922.(gv) ].
Definition tyout___polyvec_pointwise_acc : seq atype := [:: aarr U16 256 ].
Definition res___polyvec_pointwise_acc : seq var_i := [:: r_13920.(gv) ].

(* Body *)
Definition body___polyvec_pointwise_acc : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar r_13920.(gv) ] _poly_basemul [:: Pvar r_13920
                                                                    ; Psub AAscale U16 256 a_13921 (Pconst (0)%Z)
                                                                    ; Psub AAscale U16 256 b_13922 (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cfor
                              (i_13924.(gv))
                              (UpTo, Pconst (1)%Z, Pconst (3)%Z)
                              [:: MkI dummy_instr_info (Ccall [:: Lvar t_13923.(gv) ] _poly_basemul [:: Pvar t_13923
                                                                    ; Psub AAscale U16 256 a_13921 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_13924))
                                                                    ; Psub AAscale U16 256 b_13922 (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_13924)) ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r_13920.(gv) ] _poly_add2 [:: Pvar r_13920
                                                                    ; Pvar t_13923 ]) ]) ].

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
