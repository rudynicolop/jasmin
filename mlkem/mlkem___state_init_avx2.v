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

(* __state_init_avx2 *)
(* Local variables *)
Definition st_18861 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 18861).
Definition i_18862 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18862).

(* Signature *)
Definition tyin___state_init_avx2 : seq atype := [::].
Definition args___state_init_avx2 : seq var_i := [::].
Definition tyout___state_init_avx2 : seq atype := [:: aarr U256 7 ].
Definition res___state_init_avx2 : seq var_i := [:: st_18861.(gv) ].

(* Body *)
Definition body___state_init_avx2 : cmd :=
  [:: cfor
        (i_18862.(gv))
        (UpTo, Pconst (0)%Z, Pconst (7)%Z)
        [:: copn [:: Laset Aligned AAscale U256 st_18861.(gv) (Pvar i_18862) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ] ].

Definition fd___state_init_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___state_init_avx2;
    f_params := args___state_init_avx2;
    f_body := body___state_init_avx2;
    f_tyout := tyout___state_init_avx2;
    f_res := res___state_init_avx2;
    f_extra := tt;
  |}.

End IDO.
