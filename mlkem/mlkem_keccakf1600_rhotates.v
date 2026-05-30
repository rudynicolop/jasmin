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

(* keccakf1600_rhotates *)
(* Local variables *)
Definition x_3 : gvar := mk_rocq_gvar Slocal (aint) (mkident 19034).
Definition y_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 19035).
Definition r_3 : gvar := mk_rocq_gvar Slocal (aint) (mkident 19036).
Definition i_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 19037).

(* Signature *)
Definition tyin_keccakf1600_rhotates : seq atype := [:: aint; aint ].
Definition args_keccakf1600_rhotates : seq var_i := [:: x_3.(gv); y_1.(gv) ].
Definition tyout_keccakf1600_rhotates : seq atype := [:: aint ].
Definition res_keccakf1600_rhotates : seq var_i := [:: r_3.(gv) ].

(* Body *)
Definition body_keccakf1600_rhotates : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar i_0.(gv) ] keccakf1600_index [:: Pvar x_3
                                                                    ; Pvar y_1 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r_3.(gv) ] keccakf1600_rho_offsets [:: Pvar i_0 ]) ].

Definition fd_keccakf1600_rhotates : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_keccakf1600_rhotates;
    f_params := args_keccakf1600_rhotates;
    f_body := body_keccakf1600_rhotates;
    f_tyout := tyout_keccakf1600_rhotates;
    f_res := res_keccakf1600_rhotates;
    f_extra := tt;
  |}.

End IDO.
