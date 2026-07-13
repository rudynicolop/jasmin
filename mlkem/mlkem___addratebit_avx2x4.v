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

(* __addratebit_avx2x4 *)
(* Local variables *)
Definition st_9 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18559).
Definition RATE8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18560).
Definition t64_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18561).
Definition t128_2 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18562).
Definition t256_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18563).

(* Signature *)
Definition tyin___addratebit_avx2x4 : seq atype := [:: aarr U256 25; aint ].
Definition args___addratebit_avx2x4 : seq var_i :=
  [:: st_9.(gv); RATE8.(gv) ].
Definition tyout___addratebit_avx2x4 : seq atype := [:: aarr U256 25 ].
Definition res___addratebit_avx2x4 : seq var_i := [:: st_9.(gv) ].

(* Body *)
Definition body___addratebit_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar t64_1.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (1)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar t64_1.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar t64_1) (Papp1 (Oword_of_int U8) (Papp2 (Omod Unsigned (Op_int)) (Papp2 (Osub (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar RATE8)) (Pconst (1)%Z)) (Pconst (64)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar t128_2.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_1)))
    ; MkI dummy_instr_info (Copn [:: Lvar t256_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_2 ])
    ; MkI dummy_instr_info (Cassgn (Lvar t256_1.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t256_1) (Pget Aligned AAscale U256 st_9 (Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Osub (Op_int)) (Pvar RATE8) (Pconst (1)%Z)) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_9.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Osub (Op_int)) (Pvar RATE8) (Pconst (1)%Z)) (Pconst (8)%Z))) AT_none (aword U256) (Pvar t256_1)) ].

Definition fd___addratebit_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___addratebit_avx2x4;
    f_params := args___addratebit_avx2x4;
    f_body := body___addratebit_avx2x4;
    f_tyout := tyout___addratebit_avx2x4;
    f_res := res___addratebit_avx2x4;
    f_extra := tt;
  |}.

End IDO.
