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

(* __wmul_16u16 *)
(* Local variables *)
Definition x_31 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14241).
Definition y_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14242).
Definition xy0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14243).
Definition xy1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14244).
Definition xyL : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14245).
Definition xyH : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14246).

(* Signature *)
Definition tyin___wmul_16u16 : seq atype := [:: aword U256; aword U256 ].
Definition args___wmul_16u16 : seq var_i := [:: x_31.(gv); y_2.(gv) ].
Definition tyout___wmul_16u16 : seq atype := [:: aword U256; aword U256 ].
Definition res___wmul_16u16 : seq var_i := [:: xy0.(gv); xy1.(gv) ].

(* Body *)
Definition body___wmul_16u16 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar xyL.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar x_31
                                                                    ; Pvar y_2 ])
    ; MkI dummy_instr_info (Copn [:: Lvar xyH.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar x_31
                                                                    ; Pvar y_2 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar xy0.(gv); Lvar xy1.(gv) ] __w256_interleave_u16 [:: Pvar xyL
                                                                    ; Pvar xyH ]) ].

Definition fd___wmul_16u16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___wmul_16u16;
    f_params := args___wmul_16u16;
    f_body := body___wmul_16u16;
    f_tyout := tyout___wmul_16u16;
    f_res := res___wmul_16u16;
    f_extra := tt;
  |}.

End IDO.
