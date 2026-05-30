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

(* _keccakf1600_avx2 *)
(* Local variables *)
Definition state_1 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 19015).

(* Signature *)
Definition tyin__keccakf1600_avx2 : seq atype := [:: aarr U256 7 ].
Definition args__keccakf1600_avx2 : seq var_i := [:: state_1.(gv) ].
Definition tyout__keccakf1600_avx2 : seq atype := [:: aarr U256 7 ].
Definition res__keccakf1600_avx2 : seq var_i := [:: state_1.(gv) ].

(* Body *)
Definition body__keccakf1600_avx2 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar state_1.(gv) ] __keccakf1600_avx2 [:: Pvar state_1 ]) ].

Definition fd__keccakf1600_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__keccakf1600_avx2;
    f_params := args__keccakf1600_avx2;
    f_body := body__keccakf1600_avx2;
    f_tyout := tyout__keccakf1600_avx2;
    f_res := res__keccakf1600_avx2;
    f_extra := tt;
  |}.

End IDO.
