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

(* __state_init_avx2x4 *)
(* Local variables *)
Definition st_8 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18567).
Definition z256 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18568).
Definition i_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18569).

(* Signature *)
Definition tyin___state_init_avx2x4 : seq atype := [:: aarr U256 25 ].
Definition args___state_init_avx2x4 : seq var_i := [:: st_8.(gv) ].
Definition tyout___state_init_avx2x4 : seq atype := [:: aarr U256 25 ].
Definition res___state_init_avx2x4 : seq var_i := [:: st_8.(gv) ].

(* Body *)
Definition body___state_init_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar z256.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
    ; MkI dummy_instr_info (Cassgn (Lvar i_6.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (25)%Z))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_8.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar i_6))) AT_none (aword U256) (Pvar z256))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_6.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ]) ].

Definition fd___state_init_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___state_init_avx2x4;
    f_params := args___state_init_avx2x4;
    f_body := body___state_init_avx2x4;
    f_tyout := tyout___state_init_avx2x4;
    f_res := res___state_init_avx2x4;
    f_extra := tt;
  |}.

End IDO.
