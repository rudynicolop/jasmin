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

(* __schoolbook16x *)
(* Local variables *)
Definition are : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14218).
Definition aim : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14219).
Definition bre : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14220).
Definition bim : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14221).
Definition zeta : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14222).
Definition zetaqinv : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14223).
Definition qx16_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14224).
Definition qinvx16_1 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14225).
Definition sign : gvar := mk_rocq_gvar Slocal (aint) (mkident 14226).
Definition x0_14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14227).
Definition y0_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14228).
Definition zaim : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14229).
Definition ac0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14230).
Definition ac1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14231).
Definition ad0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14232).
Definition ad1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14233).
Definition bc0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14234).
Definition bc1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14235).
Definition zbd0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14236).
Definition zbd1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14237).
Definition x1_14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14238).
Definition y1_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14239).
Definition _zero_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14240).

(* Signature *)
Definition tyin___schoolbook16x : seq atype :=
  [:: aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aword U256
    ; aint ].
Definition args___schoolbook16x : seq var_i :=
  [:: are.(gv)
    ; aim.(gv)
    ; bre.(gv)
    ; bim.(gv)
    ; zeta.(gv)
    ; zetaqinv.(gv)
    ; qx16_5.(gv)
    ; qinvx16_1.(gv)
    ; sign.(gv) ].
Definition tyout___schoolbook16x : seq atype := [:: aword U256; aword U256 ].
Definition res___schoolbook16x : seq var_i := [:: x0_14.(gv); y0_1.(gv) ].

(* Body *)
Definition body___schoolbook16x : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar zaim.(gv) ] __fqmulprecomp16x [:: Pvar aim
                                                                    ; Pvar zetaqinv
                                                                    ; Pvar zeta
                                                                    ; Pvar qx16_5 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar ac0.(gv); Lvar ac1.(gv) ] __wmul_16u16 [:: Pvar are
                                                                    ; Pvar bre ])
    ; MkI dummy_instr_info (Ccall [:: Lvar ad0.(gv); Lvar ad1.(gv) ] __wmul_16u16 [:: Pvar are
                                                                    ; Pvar bim ])
    ; MkI dummy_instr_info (Ccall [:: Lvar bc0.(gv); Lvar bc1.(gv) ] __wmul_16u16 [:: Pvar aim
                                                                    ; Pvar bre ])
    ; MkI dummy_instr_info (Ccall [:: Lvar zbd0.(gv); Lvar zbd1.(gv) ] __wmul_16u16 [:: Pvar zaim
                                                                    ; Pvar bim ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oeq (Op_int)) (Pvar sign) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Copn [:: Lvar x0_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE32 U256))))) [:: Pvar ac0
                                                                    ; Pvar zbd0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar x1_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE32 U256))))) [:: Pvar ac1
                                                                    ; Pvar zbd1 ]) ]
                              [:: MkI dummy_instr_info (Copn [:: Lvar x0_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE32 U256))))) [:: Pvar ac0
                                                                    ; Pvar zbd0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar x1_14.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE32 U256))))) [:: Pvar ac1
                                                                    ; Pvar zbd1 ]) ])
    ; MkI dummy_instr_info (Copn [:: Lvar y0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE32 U256))))) [:: Pvar bc0
                                                                    ; Pvar ad0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar y1_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE32 U256))))) [:: Pvar bc1
                                                                    ; Pvar ad1 ])
    ; MkI dummy_instr_info (Copn [:: Lvar _zero_0.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar x0_14.(gv); Lvar x1_14.(gv) ] __w256_deinterleave_u16 [:: Pvar _zero_0
                                                                    ; Pvar x0_14
                                                                    ; Pvar x1_14 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar y0_1.(gv); Lvar y1_1.(gv) ] __w256_deinterleave_u16 [:: Pvar _zero_0
                                                                    ; Pvar y0_1
                                                                    ; Pvar y1_1 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar x0_14.(gv) ] __mont_red [:: Pvar x0_14
                                                                    ; Pvar x1_14
                                                                    ; Pvar qx16_5
                                                                    ; Pvar qinvx16_1 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar y0_1.(gv) ] __mont_red [:: Pvar y0_1
                                                                    ; Pvar y1_1
                                                                    ; Pvar qx16_5
                                                                    ; Pvar qinvx16_1 ]) ].

Definition fd___schoolbook16x : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___schoolbook16x;
    f_params := args___schoolbook16x;
    f_body := body___schoolbook16x;
    f_tyout := tyout___schoolbook16x;
    f_res := res___schoolbook16x;
    f_extra := tt;
  |}.

End IDO.
