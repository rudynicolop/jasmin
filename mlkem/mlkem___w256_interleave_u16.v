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

(* __w256_interleave_u16 *)
(* Local variables *)
Definition al_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14257).
Definition ah_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14258).
Definition a0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14259).
Definition a1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14260).

(* Signature *)
Definition tyin___w256_interleave_u16 : seq atype :=
  [:: aword U256; aword U256 ].
Definition args___w256_interleave_u16 : seq var_i :=
  [:: al_0.(gv); ah_0.(gv) ].
Definition tyout___w256_interleave_u16 : seq atype :=
  [:: aword U256; aword U256 ].
Definition res___w256_interleave_u16 : seq var_i := [:: a0.(gv); a1.(gv) ].

(* Body *)
Definition body___w256_interleave_u16 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar a0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE16 U256))))) [:: Pvar al_0
                                                                    ; Pvar ah_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar a1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE16 U256))))) [:: Pvar al_0
                                                                    ; Pvar ah_0 ]) ].

Definition fd___w256_interleave_u16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___w256_interleave_u16;
    f_params := args___w256_interleave_u16;
    f_body := body___w256_interleave_u16;
    f_tyout := tyout___w256_interleave_u16;
    f_res := res___w256_interleave_u16;
    f_extra := tt;
  |}.

End IDO.
