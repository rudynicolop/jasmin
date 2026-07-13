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

(* __w256_deinterleave_u16 *)
(* Local variables *)
Definition _zero : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14252).
Definition a0_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14253).
Definition a1_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14254).
Definition al_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14255).
Definition ah_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14256).

(* Signature *)
Definition tyin___w256_deinterleave_u16 : seq atype :=
  [:: aword U256; aword U256; aword U256 ].
Definition args___w256_deinterleave_u16 : seq var_i :=
  [:: _zero.(gv); a0_0.(gv); a1_0.(gv) ].
Definition tyout___w256_deinterleave_u16 : seq atype :=
  [:: aword U256; aword U256 ].
Definition res___w256_deinterleave_u16 : seq var_i :=
  [:: al_1.(gv); ah_1.(gv) ].

(* Body *)
Definition body___w256_deinterleave_u16 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar al_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE16 U256))))) [:: Pvar a0_0
                                                                    ; Pvar _zero
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar ah_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE16 U256))))) [:: Pvar a1_0
                                                                    ; Pvar _zero
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar al_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPACKUS VE32 U256))))) [:: Pvar al_1
                                                                    ; Pvar ah_1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar a0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE32 U256))))) [:: Pvar a0_0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (16)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar a1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE32 U256))))) [:: Pvar a1_0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (16)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar ah_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPACKUS VE32 U256))))) [:: Pvar a0_0
                                                                    ; Pvar a1_0 ]) ].

Definition fd___w256_deinterleave_u16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___w256_deinterleave_u16;
    f_params := args___w256_deinterleave_u16;
    f_body := body___w256_deinterleave_u16;
    f_tyout := tyout___w256_deinterleave_u16;
    f_res := res___w256_deinterleave_u16;
    f_extra := tt;
  |}.

End IDO.
