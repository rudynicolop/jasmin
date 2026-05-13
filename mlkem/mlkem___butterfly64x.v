From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* __butterfly64x *)
(* Local variables *)
Definition rl0_14045 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14045).
Definition rl1_14046 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14046).
Definition rl2_14047 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14047).
Definition rl3_14048 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14048).
Definition rh0_14049 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14049).
Definition rh1_14050 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14050).
Definition rh2_14051 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14051).
Definition rh3_14052 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14052).
Definition zl0_14053 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14053).
Definition zl1_14054 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14054).
Definition zh0_14055 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14055).
Definition zh1_14056 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14056).
Definition qx16_14057 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14057).
Definition t0_14058 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14058).
Definition t1_14059 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14059).
Definition t2_14060 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14060).
Definition t3_14061 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14061).
Definition t4_14062 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14062).
Definition t5_14063 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14063).
Definition t6_14064 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14064).
Definition t7_14065 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14065).

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
  [:: rl0_14045.(gv)
    ; rl1_14046.(gv)
    ; rl2_14047.(gv)
    ; rl3_14048.(gv)
    ; rh0_14049.(gv)
    ; rh1_14050.(gv)
    ; rh2_14051.(gv)
    ; rh3_14052.(gv)
    ; zl0_14053.(gv)
    ; zl1_14054.(gv)
    ; zh0_14055.(gv)
    ; zh1_14056.(gv)
    ; qx16_14057.(gv) ].
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
  [:: rl0_14045.(gv)
    ; rl1_14046.(gv)
    ; rl2_14047.(gv)
    ; rl3_14048.(gv)
    ; rh0_14049.(gv)
    ; rh1_14050.(gv)
    ; rh2_14051.(gv)
    ; rh3_14052.(gv) ].

(* Body *)
Definition body___butterfly64x : cmd :=
  [:: copn [:: Lvar t0_14058.(gv) ] (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl0_14053
                                                                    ; Pvar rh0_14049 ]
    ; copn [:: Lvar t1_14059.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh0_14055
                                                                    ; Pvar rh0_14049 ]
    ; copn [:: Lvar t2_14060.(gv) ] (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl0_14053
                                                                    ; Pvar rh1_14050 ]
    ; copn [:: Lvar t3_14061.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh0_14055
                                                                    ; Pvar rh1_14050 ]
    ; copn [:: Lvar t4_14062.(gv) ] (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl1_14054
                                                                    ; Pvar rh2_14051 ]
    ; copn [:: Lvar t5_14063.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh1_14056
                                                                    ; Pvar rh2_14051 ]
    ; copn [:: Lvar t6_14064.(gv) ] (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar zl1_14054
                                                                    ; Pvar rh3_14052 ]
    ; copn [:: Lvar t7_14065.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar zh1_14056
                                                                    ; Pvar rh3_14052 ]
    ; copn [:: Lvar t0_14058.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar t0_14058
                                                                    ; Pvar qx16_14057 ]
    ; copn [:: Lvar t2_14060.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar t2_14060
                                                                    ; Pvar qx16_14057 ]
    ; copn [:: Lvar t4_14062.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar t4_14062
                                                                    ; Pvar qx16_14057 ]
    ; copn [:: Lvar t6_14064.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar t6_14064
                                                                    ; Pvar qx16_14057 ]
    ; copn [:: Lvar rh1_14050.(gv) ] (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl1_14046
                                                                    ; Pvar t3_14061 ]
    ; copn [:: Lvar rl1_14046.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t3_14061
                                                                    ; Pvar rl1_14046 ]
    ; copn [:: Lvar rh0_14049.(gv) ] (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl0_14045
                                                                    ; Pvar t1_14059 ]
    ; copn [:: Lvar rl0_14045.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t1_14059
                                                                    ; Pvar rl0_14045 ]
    ; copn [:: Lvar rh3_14052.(gv) ] (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl3_14048
                                                                    ; Pvar t7_14065 ]
    ; copn [:: Lvar rl3_14048.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t7_14065
                                                                    ; Pvar rl3_14048 ]
    ; copn [:: Lvar rh2_14051.(gv) ] (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl2_14047
                                                                    ; Pvar t5_14063 ]
    ; copn [:: Lvar rl2_14047.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t5_14063
                                                                    ; Pvar rl2_14047 ]
    ; copn [:: Lvar rh0_14049.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t0_14058
                                                                    ; Pvar rh0_14049 ]
    ; copn [:: Lvar rl0_14045.(gv) ] (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl0_14045
                                                                    ; Pvar t0_14058 ]
    ; copn [:: Lvar rh1_14050.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t2_14060
                                                                    ; Pvar rh1_14050 ]
    ; copn [:: Lvar rl1_14046.(gv) ] (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl1_14046
                                                                    ; Pvar t2_14060 ]
    ; copn [:: Lvar rh2_14051.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t4_14062
                                                                    ; Pvar rh2_14051 ]
    ; copn [:: Lvar rl2_14047.(gv) ] (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl2_14047
                                                                    ; Pvar t4_14062 ]
    ; copn [:: Lvar rh3_14052.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar t6_14064
                                                                    ; Pvar rh3_14052 ]
    ; copn [:: Lvar rl3_14048.(gv) ] (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar rl3_14048
                                                                    ; Pvar t6_14064 ] ].

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
