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

(* keccakf1600_rho_offsets *)
(* Local variables *)
Definition i : gvar := mk_rocq_gvar Slocal (aint) (mkident 19038).
Definition r_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 19039).
Definition x_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 19040).
Definition y_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 19041).
Definition t_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 19042).
Definition z : gvar := mk_rocq_gvar Slocal (aint) (mkident 19043).

(* Signature *)
Definition tyin_keccakf1600_rho_offsets : seq atype := [:: aint ].
Definition args_keccakf1600_rho_offsets : seq var_i := [:: i.(gv) ].
Definition tyout_keccakf1600_rho_offsets : seq atype := [:: aint ].
Definition res_keccakf1600_rho_offsets : seq var_i := [:: r_2.(gv) ].

(* Body *)
Definition body_keccakf1600_rho_offsets : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar r_2.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar x_2.(gv)) AT_none (aint) (Pconst (1)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar y_0.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cfor
                              (t_0.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (24)%Z)
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Oeq (Op_int)) (Pvar i) (Papp2 (Oadd (Op_int)) (Pvar x_2) (Papp2 (Omul (Op_int)) (Pconst (5)%Z) (Pvar y_0))))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar r_2.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Omul (Op_int)) (Papp2 (Oadd (Op_int)) (Pvar t_0) (Pconst (1)%Z)) (Papp2 (Oadd (Op_int)) (Pvar t_0) (Pconst (2)%Z))) (Pconst (2)%Z)) (Pconst (64)%Z))) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar z.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pvar x_2)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pvar y_0))) (Pconst (5)%Z)))
                                ; MkI dummy_instr_info (Cassgn (Lvar x_2.(gv)) AT_none (aint) (Pvar y_0))
                                ; MkI dummy_instr_info (Cassgn (Lvar y_0.(gv)) AT_none (aint) (Pvar z)) ]) ].

Definition fd_keccakf1600_rho_offsets : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_keccakf1600_rho_offsets;
    f_params := args_keccakf1600_rho_offsets;
    f_body := body_keccakf1600_rho_offsets;
    f_tyout := tyout_keccakf1600_rho_offsets;
    f_res := res_keccakf1600_rho_offsets;
    f_extra := tt;
  |}.

End IDO.
