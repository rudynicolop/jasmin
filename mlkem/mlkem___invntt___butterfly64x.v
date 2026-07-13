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

(* __invntt___butterfly64x *)
(* Local variables *)
Definition rl0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14084).
Definition rl1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14085).
Definition rl2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14086).
Definition rl3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14087).
Definition rh0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14088).
Definition rh1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14089).
Definition rh2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14090).
Definition rh3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14091).
Definition zl0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14092).
Definition zl1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14093).
Definition zh0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14094).
Definition zh1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14095).
Definition qx16_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14096).
Definition t0_27 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14097).
Definition t1_27 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14098).
Definition t2_25 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14099).
Definition t3_25 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14100).

(* Signature *)
Definition tyin___invntt___butterfly64x : seq atype :=
  [:: aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256 ].
Definition args___invntt___butterfly64x : seq var_i :=
  [:: rl0.(gv)
    ; rl1.(gv)
    ; rl2.(gv)
    ; rl3.(gv)
    ; rh0.(gv)
    ; rh1.(gv)
    ; rh2.(gv)
    ; rh3.(gv)
    ; zl0.(gv)
    ; zl1.(gv)
    ; zh0.(gv)
    ; zh1.(gv)
    ; qx16_8.(gv) ].
Definition tyout___invntt___butterfly64x : seq atype :=
  [:: aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256 ].
Definition res___invntt___butterfly64x : seq var_i :=
  [:: rl0.(gv)
    ; rl1.(gv)
    ; rl2.(gv)
    ; rl3.(gv)
    ; rh0.(gv)
    ; rh1.(gv)
    ; rh2.(gv)
    ; rh3.(gv) ].

(* Body *)
Definition body___invntt___butterfly64x : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar t0_27.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl0
                                                                    ; Pvar rh0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t1_27.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl1
                                                                    ; Pvar rh1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t2_25.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl2
                                                                    ; Pvar rh2 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar rh0
                                                                    ; Pvar rl0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar rh1
                                                                    ; Pvar rl1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl0
                                                                    ; Pvar t0_27 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar rh2
                                                                    ; Pvar rl2 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl0
                                                                    ; Pvar t1_27 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t3_25.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl3
                                                                    ; Pvar rh3 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar rh3
                                                                    ; Pvar rl3 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl1
                                                                    ; Pvar t2_25 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl1
                                                                    ; Pvar t3_25 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t0_27.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh0
                                                                    ; Pvar t0_27 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t1_27.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh0
                                                                    ; Pvar t1_27 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t2_25.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh1
                                                                    ; Pvar t2_25 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t3_25.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh1
                                                                    ; Pvar t3_25 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar qx16_8
                                                                    ; Pvar rh0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar qx16_8
                                                                    ; Pvar rh1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar qx16_8
                                                                    ; Pvar rh2 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar qx16_8
                                                                    ; Pvar rh3 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar t0_27
                                                                    ; Pvar rh0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar t1_27
                                                                    ; Pvar rh1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar t2_25
                                                                    ; Pvar rh2 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar t3_25
                                                                    ; Pvar rh3 ]) ].

Definition fd___invntt___butterfly64x : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___invntt___butterfly64x;
    f_params := args___invntt___butterfly64x;
    f_body := body___invntt___butterfly64x;
    f_tyout := tyout___invntt___butterfly64x;
    f_res := res___invntt___butterfly64x;
    f_extra := tt;
  |}.

End IDO.
