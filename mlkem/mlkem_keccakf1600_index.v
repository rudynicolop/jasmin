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

(* keccakf1600_index *)
(* Local variables *)
Definition x_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 19044).
Definition y : gvar := mk_rocq_gvar Slocal (aint) (mkident 19045).
Definition r_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 19046).

(* Signature *)
Definition tyin_keccakf1600_index : seq atype := [:: aint; aint ].
Definition args_keccakf1600_index : seq var_i := [:: x_1.(gv); y.(gv) ].
Definition tyout_keccakf1600_index : seq atype := [:: aint ].
Definition res_keccakf1600_index : seq var_i := [:: r_1.(gv) ].

(* Body *)
Definition body_keccakf1600_index : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar r_1.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar x_1) (Pconst (5)%Z)) (Papp2 (Omul (Op_int)) (Pconst (5)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar y) (Pconst (5)%Z))))) ].

Definition fd_keccakf1600_index : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_keccakf1600_index;
    f_params := args_keccakf1600_index;
    f_body := body_keccakf1600_index;
    f_tyout := tyout_keccakf1600_index;
    f_res := res_keccakf1600_index;
    f_extra := tt;
  |}.

End IDO.
