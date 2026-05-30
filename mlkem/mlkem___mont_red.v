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

(* __mont_red *)
(* Local variables *)
Definition lo : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14247).
Definition hi : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14248).
Definition qx16_4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14249).
Definition qinvx16_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14250).
Definition m : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14251).

(* Signature *)
Definition tyin___mont_red : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition args___mont_red : seq var_i :=
  [:: lo.(gv); hi.(gv); qx16_4.(gv); qinvx16_0.(gv) ].
Definition tyout___mont_red : seq atype := [:: aword U256 ].
Definition res___mont_red : seq var_i := [:: lo.(gv) ].

(* Body *)
Definition body___mont_red : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar m.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar lo
                                                                    ; Pvar qinvx16_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar m.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar m
                                                                    ; Pvar qx16_4 ])
    ; MkI dummy_instr_info (Copn [:: Lvar lo.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar hi
                                                                    ; Pvar m ]) ].

Definition fd___mont_red : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___mont_red;
    f_params := args___mont_red;
    f_body := body___mont_red;
    f_tyout := tyout___mont_red;
    f_res := res___mont_red;
    f_extra := tt;
  |}.

End IDO.
