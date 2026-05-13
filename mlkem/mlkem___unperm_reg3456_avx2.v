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

(* __unperm_reg3456_avx2 *)
(* Local variables *)
Definition st3_18838 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18838).
Definition st4_18839 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18839).
Definition st5_18840 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18840).
Definition st6_18841 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18841).
Definition r3_18842 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18842).
Definition r4_18843 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18843).
Definition r5_18844 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18844).
Definition r6_18845 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18845).
Definition t256_0_18846 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18846).
Definition t256_1_18847 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18847).
Definition t256_2_18848 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18848).
Definition t256_3_18849 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18849).

(* Signature *)
Definition tyin___unperm_reg3456_avx2 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition args___unperm_reg3456_avx2 : seq var_i :=
  [:: st3_18838.(gv); st4_18839.(gv); st5_18840.(gv); st6_18841.(gv) ].
Definition tyout___unperm_reg3456_avx2 : seq atype :=
  [:: aword U256; aword U256; aword U256; aword U256 ].
Definition res___unperm_reg3456_avx2 : seq var_i :=
  [:: r3_18842.(gv); r4_18843.(gv); r5_18844.(gv); r6_18845.(gv) ].

(* Body *)
Definition body___unperm_reg3456_avx2 : cmd :=
  [:: copn [:: Lvar t256_0_18846.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar st3_18838
                                                                    ; Pvar st4_18839
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t256_1_18847.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar st4_18839
                                                                    ; Pvar st3_18838
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t256_2_18848.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar st5_18840
                                                                    ; Pvar st6_18841
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t256_3_18849.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar st6_18841
                                                                    ; Pvar st5_18840
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar r3_18842.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_18846
                                                                    ; Pvar t256_3_18849
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
    ; copn [:: Lvar r4_18843.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_18849
                                                                    ; Pvar t256_1_18847
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
    ; copn [:: Lvar r5_18844.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_18848
                                                                    ; Pvar t256_0_18846
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
    ; copn [:: Lvar r6_18845.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_18847
                                                                    ; Pvar t256_2_18848
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ] ].

Definition fd___unperm_reg3456_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___unperm_reg3456_avx2;
    f_params := args___unperm_reg3456_avx2;
    f_body := body___unperm_reg3456_avx2;
    f_tyout := tyout___unperm_reg3456_avx2;
    f_res := res___unperm_reg3456_avx2;
    f_extra := tt;
  |}.

End IDO.
