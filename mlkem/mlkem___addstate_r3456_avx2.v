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

(* __addstate_r3456_avx2 *)
(* Local variables *)
Definition st_2 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 18833).
Definition r3_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18834).
Definition r4_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18835).
Definition r5_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18836).
Definition r6_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18837).

(* Signature *)
Definition tyin___addstate_r3456_avx2 : seq atype :=
  [:: aarr U256 7; aword U256; aword U256; aword U256; aword U256 ].
Definition args___addstate_r3456_avx2 : seq var_i :=
  [:: st_2.(gv); r3_3.(gv); r4_3.(gv); r5_3.(gv); r6_3.(gv) ].
Definition tyout___addstate_r3456_avx2 : seq atype := [:: aarr U256 7 ].
Definition res___addstate_r3456_avx2 : seq var_i := [:: st_2.(gv) ].

(* Body *)
Definition body___addstate_r3456_avx2 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar r3_3.(gv)
                                    ; Lvar r4_3.(gv)
                                    ; Lvar r5_3.(gv)
                                    ; Lvar r6_3.(gv) ] __perm_reg3456_avx2 [:: Pvar r3_3
                                                                    ; Pvar r4_3
                                                                    ; Pvar r5_3
                                                                    ; Pvar r6_3 ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_2.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_2 (Pconst (3)%Z)) (Pvar r3_3)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_2.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_2 (Pconst (4)%Z)) (Pvar r4_3)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_2.(gv) (Pconst (5)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_2 (Pconst (5)%Z)) (Pvar r5_3)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_2.(gv) (Pconst (6)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_2 (Pconst (6)%Z)) (Pvar r6_3))) ].

Definition fd___addstate_r3456_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___addstate_r3456_avx2;
    f_params := args___addstate_r3456_avx2;
    f_body := body___addstate_r3456_avx2;
    f_tyout := tyout___addstate_r3456_avx2;
    f_res := res___addstate_r3456_avx2;
    f_extra := tt;
  |}.

End IDO.
