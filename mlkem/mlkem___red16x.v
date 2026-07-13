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

(* __red16x *)
(* Local variables *)
Definition r_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19059).
Definition qx16_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19060).
Definition vx16 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19061).
Definition x : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19062).

(* Signature *)
Definition tyin___red16x : seq atype :=
  [:: aword U256; aword U256; aword U256 ].
Definition args___red16x : seq var_i :=
  [:: r_0.(gv); qx16_0.(gv); vx16.(gv) ].
Definition tyout___red16x : seq atype := [:: aword U256 ].
Definition res___red16x : seq var_i := [:: r_0.(gv) ].

(* Body *)
Definition body___red16x : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar x.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar r_0
                                                                    ; Pvar vx16 ])
    ; MkI dummy_instr_info (Copn [:: Lvar x.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRA VE16 U256))))) [:: Pvar x
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (10)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar x.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar x
                                                                    ; Pvar qx16_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar r_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar r_0
                                                                    ; Pvar x ]) ].

Definition fd___red16x : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___red16x;
    f_params := args___red16x;
    f_body := body___red16x;
    f_tyout := tyout___red16x;
    f_res := res___red16x;
    f_extra := tt;
  |}.

End IDO.
