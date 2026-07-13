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

(* __shuffle8 *)
(* Local variables *)
Definition a : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19097).
Definition b : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19098).
Definition r0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19099).
Definition r1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19100).

(* Signature *)
Definition tyin___shuffle8 : seq atype := [:: aword U256; aword U256 ].
Definition args___shuffle8 : seq var_i := [:: a.(gv); b.(gv) ].
Definition tyout___shuffle8 : seq atype := [:: aword U256; aword U256 ].
Definition res___shuffle8 : seq var_i := [:: r0.(gv); r1.(gv) ].

(* Body *)
Definition body___shuffle8 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar r0.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar a
                                                                    ; Pvar b
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar r1.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar a
                                                                    ; Pvar b
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (49)%Z) ]) ].

Definition fd___shuffle8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___shuffle8;
    f_params := args___shuffle8;
    f_body := body___shuffle8;
    f_tyout := tyout___shuffle8;
    f_res := res___shuffle8;
    f_extra := tt;
  |}.

End IDO.
