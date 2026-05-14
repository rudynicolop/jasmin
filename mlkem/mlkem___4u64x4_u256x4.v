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

(* __4u64x4_u256x4 *)
(* Local variables *)
Definition y0_18612 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18612).
Definition y1_18613 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18613).
Definition y2_18614 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18614).
Definition y3_18615 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18615).
Definition x0_18616 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18616).
Definition x1_18617 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18617).
Definition x2_18618 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18618).
Definition x3_18619 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18619).

(* Signature *)
Definition tyin___4u64x4_u256x4 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition args___4u64x4_u256x4 : seq var_i :=
  [:: y0_18612.(gv); y1_18613.(gv); y2_18614.(gv); y3_18615.(gv) ].
Definition tyout___4u64x4_u256x4 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition res___4u64x4_u256x4 : seq var_i :=
  [:: y0_18612.(gv); y1_18613.(gv); y2_18614.(gv); y3_18615.(gv) ].

(* Body *)
Definition body___4u64x4_u256x4 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar x0_18616.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y0_18612
                                                                    ; Pvar y2_18614
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar x1_18617.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y1_18613
                                                                    ; Pvar y3_18615
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (32)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar x2_18618.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y0_18612
                                                                    ; Pvar y2_18614
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (49)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar x3_18619.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar y1_18613
                                                                    ; Pvar y3_18615
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (49)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar y0_18612.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE64 U256))))) [:: Pvar x0_18616
                                                                    ; Pvar x1_18617 ])
    ; MkI dummy_instr_info (Copn [:: Lvar y1_18613.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U256))))) [:: Pvar x0_18616
                                                                    ; Pvar x1_18617 ])
    ; MkI dummy_instr_info (Copn [:: Lvar y2_18614.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE64 U256))))) [:: Pvar x2_18618
                                                                    ; Pvar x3_18619 ])
    ; MkI dummy_instr_info (Copn [:: Lvar y3_18615.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U256))))) [:: Pvar x2_18618
                                                                    ; Pvar x3_18619 ]) ].

Definition fd___4u64x4_u256x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___4u64x4_u256x4;
    f_params := args___4u64x4_u256x4;
    f_body := body___4u64x4_u256x4;
    f_tyout := tyout___4u64x4_u256x4;
    f_res := res___4u64x4_u256x4;
    f_extra := tt;
  |}.

End IDO.
