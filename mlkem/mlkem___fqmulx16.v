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

(* __fqmulx16 *)
(* Local variables *)
Definition a_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19047).
Definition b_4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19048).
Definition qx16_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19049).
Definition qinvx16 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19050).
Definition rd : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19051).
Definition rhi : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19052).
Definition rlo : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19053).

(* Signature *)
Definition tyin___fqmulx16 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition args___fqmulx16 : seq var_i :=
  [:: a_3.(gv); b_4.(gv); qx16_2.(gv); qinvx16.(gv) ].
Definition tyout___fqmulx16 : seq atype := [:: aword U256 ].
Definition res___fqmulx16 : seq var_i := [:: rd.(gv) ].

(* Body *)
Definition body___fqmulx16 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar rhi.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar a_3
                                                                    ; Pvar b_4 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rlo.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar a_3
                                                                    ; Pvar b_4 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rlo.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar rlo
                                                                    ; Pvar qinvx16 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rlo.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar rlo
                                                                    ; Pvar qx16_2 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rd.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rhi
                                                                    ; Pvar rlo ]) ].

Definition fd___fqmulx16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___fqmulx16;
    f_params := args___fqmulx16;
    f_body := body___fqmulx16;
    f_tyout := tyout___fqmulx16;
    f_res := res___fqmulx16;
    f_extra := tt;
  |}.

End IDO.
