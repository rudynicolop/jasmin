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

(* __shuffle1 *)
(* Local variables *)
Definition a_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19083).
Definition b_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19084).
Definition r0_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19085).
Definition r1_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19086).
Definition t0_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19087).
Definition t1_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19088).

(* Signature *)
Definition tyin___shuffle1 : seq atype := [:: aword U256; aword U256 ].
Definition args___shuffle1 : seq var_i := [:: a_2.(gv); b_2.(gv) ].
Definition tyout___shuffle1 : seq atype := [:: aword U256; aword U256 ].
Definition res___shuffle1 : seq var_i := [:: r0_1.(gv); r1_1.(gv) ].

(* Body *)
Definition body___shuffle1 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar t0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE32 U256))))) [:: Pvar b_2
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (16)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar r0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE16 U256))))) [:: Pvar a_2
                                                                    ; Pvar t0_0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar t1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE32 U256))))) [:: Pvar a_2
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (16)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar r1_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE16 U256))))) [:: Pvar t1_0
                                                                    ; Pvar b_2
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ]) ].

Definition fd___shuffle1 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___shuffle1;
    f_params := args___shuffle1;
    f_body := body___shuffle1;
    f_tyout := tyout___shuffle1;
    f_res := res___shuffle1;
    f_extra := tt;
  |}.

End IDO.
