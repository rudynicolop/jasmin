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

(* __shuffle2 *)
(* Local variables *)
Definition a_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19089).
Definition b_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19090).
Definition t0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19091).
Definition t1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19092).

(* Signature *)
Definition tyin___shuffle2 : seq atype := [:: aword U256; aword U256 ].
Definition args___shuffle2 : seq var_i := [:: a_1.(gv); b_1.(gv) ].
Definition tyout___shuffle2 : seq atype := [:: aword U256; aword U256 ].
Definition res___shuffle2 : seq var_i := [:: t0.(gv); t1.(gv) ].

(* Body *)
Definition body___shuffle2 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar t0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VMOVSLDUP U256))))) [:: Pvar b_1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar a_1
                                                                    ; Pvar t0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar a_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pvar a_1
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar t1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar a_1
                                                                    ; Pvar b_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ]) ].

Definition fd___shuffle2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___shuffle2;
    f_params := args___shuffle2;
    f_body := body___shuffle2;
    f_tyout := tyout___shuffle2;
    f_res := res___shuffle2;
    f_extra := tt;
  |}.

End IDO.
