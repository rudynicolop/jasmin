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

(* __butterfly64x *)
(* Local variables *)
Definition rl0_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14045).
Definition rl1_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14046).
Definition rl2_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14047).
Definition rl3_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14048).
Definition rh0_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14049).
Definition rh1_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14050).
Definition rh2_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14051).
Definition rh3_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14052).
Definition zl0_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14053).
Definition zl1_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14054).
Definition zh0_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14055).
Definition zh1_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14056).
Definition qx16_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14057).
Definition t0_28 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14058).
Definition t1_28 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14059).
Definition t2_26 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14060).
Definition t3_26 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14061).
Definition t4_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14062).
Definition t5_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14063).
Definition t6_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14064).
Definition t7_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14065).

(* Signature *)
Definition tyin___butterfly64x : seq atype :=
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
Definition args___butterfly64x : seq var_i :=
  [:: rl0_0.(gv)
    ; rl1_0.(gv)
    ; rl2_0.(gv)
    ; rl3_0.(gv)
    ; rh0_0.(gv)
    ; rh1_0.(gv)
    ; rh2_0.(gv)
    ; rh3_0.(gv)
    ; zl0_0.(gv)
    ; zl1_0.(gv)
    ; zh0_0.(gv)
    ; zh1_0.(gv)
    ; qx16_10.(gv) ].
Definition tyout___butterfly64x : seq atype :=
  [:: aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256 ].
Definition res___butterfly64x : seq var_i :=
  [:: rl0_0.(gv)
    ; rl1_0.(gv)
    ; rl2_0.(gv)
    ; rl3_0.(gv)
    ; rh0_0.(gv)
    ; rh1_0.(gv)
    ; rh2_0.(gv)
    ; rh3_0.(gv) ].

(* Body *)
Definition body___butterfly64x : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar t0_28.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl0_0
                                                                    ; Pvar rh0_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t1_28.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh0_0
                                                                    ; Pvar rh0_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t2_26.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl0_0
                                                                    ; Pvar rh1_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t3_26.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh0_0
                                                                    ; Pvar rh1_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t4_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl1_0
                                                                    ; Pvar rh2_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t5_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh1_0
                                                                    ; Pvar rh2_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t6_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl1_0
                                                                    ; Pvar rh3_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t7_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh1_0
                                                                    ; Pvar rh3_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t0_28.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar t0_28
                                                                    ; Pvar qx16_10 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t2_26.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar t2_26
                                                                    ; Pvar qx16_10 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t4_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar t4_1
                                                                    ; Pvar qx16_10 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t6_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar t6_1
                                                                    ; Pvar qx16_10 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl1_0
                                                                    ; Pvar t3_26 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t3_26
                                                                    ; Pvar rl1_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl0_0
                                                                    ; Pvar t1_28 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t1_28
                                                                    ; Pvar rl0_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh3_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl3_0
                                                                    ; Pvar t7_1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl3_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t7_1
                                                                    ; Pvar rl3_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl2_0
                                                                    ; Pvar t5_1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t5_1
                                                                    ; Pvar rl2_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t0_28
                                                                    ; Pvar rh0_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl0_0
                                                                    ; Pvar t0_28 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t2_26
                                                                    ; Pvar rh1_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl1_0
                                                                    ; Pvar t2_26 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t4_1
                                                                    ; Pvar rh2_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl2_0
                                                                    ; Pvar t4_1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rh3_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t6_1
                                                                    ; Pvar rh3_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar rl3_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl3_0
                                                                    ; Pvar t6_1 ]) ].

Definition fd___butterfly64x : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___butterfly64x;
    f_params := args___butterfly64x;
    f_body := body___butterfly64x;
    f_tyout := tyout___butterfly64x;
    f_res := res___butterfly64x;
    f_extra := tt;
  |}.

End IDO.
