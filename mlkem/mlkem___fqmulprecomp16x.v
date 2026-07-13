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

(* __fqmulprecomp16x *)
(* Local variables *)
Definition b_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19054).
Definition al : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19055).
Definition ah : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19056).
Definition qx16_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19057).
Definition x_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19058).

(* Signature *)
Definition tyin___fqmulprecomp16x : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition args___fqmulprecomp16x : seq var_i :=
  [:: b_3.(gv); al.(gv); ah.(gv); qx16_1.(gv) ].
Definition tyout___fqmulprecomp16x : seq atype := [:: aword U256 ].
Definition res___fqmulprecomp16x : seq var_i := [:: b_3.(gv) ].

(* Body *)
Definition body___fqmulprecomp16x : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar x_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar al
                                                                    ; Pvar b_3 ])
    ; MkI dummy_instr_info (Copn [:: Lvar b_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar ah
                                                                    ; Pvar b_3 ])
    ; MkI dummy_instr_info (Copn [:: Lvar x_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar x_0
                                                                    ; Pvar qx16_1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar b_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar b_3
                                                                    ; Pvar x_0 ]) ].

Definition fd___fqmulprecomp16x : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___fqmulprecomp16x;
    f_params := args___fqmulprecomp16x;
    f_body := body___fqmulprecomp16x;
    f_tyout := tyout___fqmulprecomp16x;
    f_res := res___fqmulprecomp16x;
    f_extra := tt;
  |}.

End IDO.
