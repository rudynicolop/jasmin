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

(* j__keccakf1600_avx2x4_ *)
(* Local variables *)
Definition a_7 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18648).

(* Signature *)
Definition tyin_j__keccakf1600_avx2x4_ : seq atype := [:: aarr U256 25 ].
Definition args_j__keccakf1600_avx2x4_ : seq var_i := [:: a_7.(gv) ].
Definition tyout_j__keccakf1600_avx2x4_ : seq atype := [:: aarr U256 25 ].
Definition res_j__keccakf1600_avx2x4_ : seq var_i := [:: a_7.(gv) ].

(* Body *)
Definition body_j__keccakf1600_avx2x4_ : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar a_7.(gv)) AT_none (aarr U256 25) (Pvar a_7))
    ; MkI dummy_instr_info (Ccall [:: Lvar a_7.(gv) ] _keccakf1600_avx2x4 [:: Pvar a_7 ])
    ; MkI dummy_instr_info (Cassgn (Lvar a_7.(gv)) AT_none (aarr U256 25) (Pvar a_7)) ].

Definition fd_j__keccakf1600_avx2x4_ : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_j__keccakf1600_avx2x4_;
    f_params := args_j__keccakf1600_avx2x4_;
    f_body := body_j__keccakf1600_avx2x4_;
    f_tyout := tyout_j__keccakf1600_avx2x4_;
    f_res := res_j__keccakf1600_avx2x4_;
    f_extra := tt;
  |}.

End IDO.
