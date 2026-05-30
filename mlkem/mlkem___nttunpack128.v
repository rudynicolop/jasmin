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

(* __nttunpack128 *)
(* Local variables *)
Definition r0_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19075).
Definition r1_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19076).
Definition r2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19077).
Definition r3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19078).
Definition r4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19079).
Definition r5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19080).
Definition r6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19081).
Definition r7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19082).

(* Signature *)
Definition tyin___nttunpack128 : seq atype :=
  [:: aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256 ].
Definition args___nttunpack128 : seq var_i :=
  [:: r0_2.(gv)
    ; r1_2.(gv)
    ; r2.(gv)
    ; r3.(gv)
    ; r4.(gv)
    ; r5.(gv)
    ; r6.(gv)
    ; r7.(gv) ].
Definition tyout___nttunpack128 : seq atype :=
  [:: aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256 ].
Definition res___nttunpack128 : seq var_i :=
  [:: r0_2.(gv)
    ; r4.(gv)
    ; r1_2.(gv)
    ; r5.(gv)
    ; r2.(gv)
    ; r6.(gv)
    ; r3.(gv)
    ; r7.(gv) ].

(* Body *)
Definition body___nttunpack128 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar r0_2.(gv); Lvar r4.(gv) ] __shuffle8 [:: Pvar r0_2
                                                                    ; Pvar r4 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r1_2.(gv); Lvar r5.(gv) ] __shuffle8 [:: Pvar r1_2
                                                                    ; Pvar r5 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r2.(gv); Lvar r6.(gv) ] __shuffle8 [:: Pvar r2
                                                                    ; Pvar r6 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r3.(gv); Lvar r7.(gv) ] __shuffle8 [:: Pvar r3
                                                                    ; Pvar r7 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r0_2.(gv); Lvar r2.(gv) ] __shuffle4 [:: Pvar r0_2
                                                                    ; Pvar r2 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r4.(gv); Lvar r6.(gv) ] __shuffle4 [:: Pvar r4
                                                                    ; Pvar r6 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r1_2.(gv); Lvar r3.(gv) ] __shuffle4 [:: Pvar r1_2
                                                                    ; Pvar r3 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r5.(gv); Lvar r7.(gv) ] __shuffle4 [:: Pvar r5
                                                                    ; Pvar r7 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r0_2.(gv); Lvar r1_2.(gv) ] __shuffle2 [:: Pvar r0_2
                                                                    ; Pvar r1_2 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r2.(gv); Lvar r3.(gv) ] __shuffle2 [:: Pvar r2
                                                                    ; Pvar r3 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r4.(gv); Lvar r5.(gv) ] __shuffle2 [:: Pvar r4
                                                                    ; Pvar r5 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r6.(gv); Lvar r7.(gv) ] __shuffle2 [:: Pvar r6
                                                                    ; Pvar r7 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r0_2.(gv); Lvar r4.(gv) ] __shuffle1 [:: Pvar r0_2
                                                                    ; Pvar r4 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r1_2.(gv); Lvar r5.(gv) ] __shuffle1 [:: Pvar r1_2
                                                                    ; Pvar r5 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r2.(gv); Lvar r6.(gv) ] __shuffle1 [:: Pvar r2
                                                                    ; Pvar r6 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar r3.(gv); Lvar r7.(gv) ] __shuffle1 [:: Pvar r3
                                                                    ; Pvar r7 ]) ].

Definition fd___nttunpack128 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___nttunpack128;
    f_params := args___nttunpack128;
    f_body := body___nttunpack128;
    f_tyout := tyout___nttunpack128;
    f_res := res___nttunpack128;
    f_extra := tt;
  |}.

End IDO.
