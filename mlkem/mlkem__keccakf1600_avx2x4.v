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

(* _keccakf1600_avx2x4 *)
(* Local variables *)
Definition a_6 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18649).

(* Signature *)
Definition tyin__keccakf1600_avx2x4 : seq atype := [:: aarr U256 25 ].
Definition args__keccakf1600_avx2x4 : seq var_i := [:: a_6.(gv) ].
Definition tyout__keccakf1600_avx2x4 : seq atype := [:: aarr U256 25 ].
Definition res__keccakf1600_avx2x4 : seq var_i := [:: a_6.(gv) ].

(* Body *)
Definition body__keccakf1600_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar a_6.(gv) ] __keccakf1600_avx2x4 [:: Pvar a_6 ]) ].

Definition fd__keccakf1600_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__keccakf1600_avx2x4;
    f_params := args__keccakf1600_avx2x4;
    f_body := body__keccakf1600_avx2x4;
    f_tyout := tyout__keccakf1600_avx2x4;
    f_res := res__keccakf1600_avx2x4;
    f_extra := tt;
  |}.

End IDO.
