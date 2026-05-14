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

(* __csubq *)
(* Local variables *)
Definition r : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19063).
Definition qx16 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19064).
Definition t : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19065).

(* Signature *)
Definition tyin___csubq : seq atype := [:: aword U256; aword U256 ].
Definition args___csubq : seq var_i := [:: r.(gv); qx16.(gv) ].
Definition tyout___csubq : seq atype := [:: aword U256 ].
Definition res___csubq : seq var_i := [:: r.(gv) ].

(* Body *)
Definition body___csubq : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar r.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar r
                                                                    ; Pvar qx16 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRA VE16 U256))))) [:: Pvar r
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (15)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar t.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar t
                                                                    ; Pvar qx16 ])
    ; MkI dummy_instr_info (Copn [:: Lvar r.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t
                                                                    ; Pvar r ]) ].

Definition fd___csubq : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___csubq;
    f_params := args___csubq;
    f_body := body___csubq;
    f_tyout := tyout___csubq;
    f_res := res___csubq;
    f_extra := tt;
  |}.

End IDO.
