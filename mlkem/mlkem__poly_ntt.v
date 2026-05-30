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

(* _poly_ntt *)
(* Local variables *)
Definition rp_10 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14029).
Definition qx16_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14030).
Definition zeta0_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14031).
Definition zeta1_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14032).
Definition r0_18 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14033).
Definition r1_18 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14034).
Definition r2_15 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14035).
Definition r3_18 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14036).
Definition r4_17 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14037).
Definition r5_17 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14038).
Definition r6_17 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14039).
Definition r7_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14040).
Definition i_80 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14041).
Definition zeta2_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14042).
Definition zeta3_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14043).
Definition vx16_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14044).

(* Signature *)
Definition tyin__poly_ntt : seq atype := [:: aarr U16 256 ].
Definition args__poly_ntt : seq var_i := [:: rp_10.(gv) ].
Definition tyout__poly_ntt : seq atype := [:: aarr U16 256 ].
Definition res__poly_ntt : seq var_i := [:: rp_10.(gv) ].

(* Body *)
Definition body__poly_ntt : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar qx16_11.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jqx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar zeta0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Aligned AAscale U32 jzetas_exp (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar zeta1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Aligned AAscale U32 jzetas_exp (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar r0_18.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r1_18.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r2_15.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r3_18.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r4_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r5_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r6_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r7_2.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                    ; Lvar r1_18.(gv)
                                    ; Lvar r2_15.(gv)
                                    ; Lvar r3_18.(gv)
                                    ; Lvar r4_17.(gv)
                                    ; Lvar r5_17.(gv)
                                    ; Lvar r6_17.(gv)
                                    ; Lvar r7_2.(gv) ] __butterfly64x [:: Pvar r0_18
                                                                    ; Pvar r1_18
                                                                    ; Pvar r2_15
                                                                    ; Pvar r3_18
                                                                    ; Pvar r4_17
                                                                    ; Pvar r5_17
                                                                    ; Pvar r6_17
                                                                    ; Pvar r7_2
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar qx16_11 ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))) AT_none (aword U256) (Pvar r0_18))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))) AT_none (aword U256) (Pvar r1_18))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))) AT_none (aword U256) (Pvar r2_15))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))) AT_none (aword U256) (Pvar r3_18))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))) AT_none (aword U256) (Pvar r4_17))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))) AT_none (aword U256) (Pvar r5_17))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))) AT_none (aword U256) (Pvar r6_17))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))) AT_none (aword U256) (Pvar r7_2))
    ; MkI dummy_instr_info (Cassgn (Lvar r0_18.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r1_18.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r2_15.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r3_18.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r4_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r5_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r6_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r7_2.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                    ; Lvar r1_18.(gv)
                                    ; Lvar r2_15.(gv)
                                    ; Lvar r3_18.(gv)
                                    ; Lvar r4_17.(gv)
                                    ; Lvar r5_17.(gv)
                                    ; Lvar r6_17.(gv)
                                    ; Lvar r7_2.(gv) ] __butterfly64x [:: Pvar r0_18
                                                                    ; Pvar r1_18
                                                                    ; Pvar r2_15
                                                                    ; Pvar r3_18
                                                                    ; Pvar r4_17
                                                                    ; Pvar r5_17
                                                                    ; Pvar r6_17
                                                                    ; Pvar r7_2
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar qx16_11 ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))) AT_none (aword U256) (Pvar r4_17))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))) AT_none (aword U256) (Pvar r5_17))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))) AT_none (aword U256) (Pvar r6_17))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))) AT_none (aword U256) (Pvar r7_2))
    ; MkI dummy_instr_info (Cfor
                              (i_80.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (2)%Z)
                              [:: MkI dummy_instr_info (Copn [:: Lvar zeta0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (8)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80))) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar zeta1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (12)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80))) ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oeq (Op_int)) (Pvar i_80) (Pconst (0)%Z))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar r4_17.(gv)) AT_none (aword U256) (Pvar r0_18))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r5_17.(gv)) AT_none (aword U256) (Pvar r1_18))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r6_17.(gv)) AT_none (aword U256) (Pvar r2_15))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r7_2.(gv)) AT_none (aword U256) (Pvar r3_18)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar r4_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r5_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r6_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r7_2.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80))))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar r0_18.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r1_18.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_15.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r3_18.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_10 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                                                ; Lvar r1_18.(gv)
                                                                ; Lvar r2_15.(gv)
                                                                ; Lvar r3_18.(gv)
                                                                ; Lvar r4_17.(gv)
                                                                ; Lvar r5_17.(gv)
                                                                ; Lvar r6_17.(gv)
                                                                ; Lvar r7_2.(gv) ] __butterfly64x [:: Pvar r0_18
                                                                    ; Pvar r1_18
                                                                    ; Pvar r2_15
                                                                    ; Pvar r3_18
                                                                    ; Pvar r4_17
                                                                    ; Pvar r5_17
                                                                    ; Pvar r6_17
                                                                    ; Pvar r7_2
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar qx16_11 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta0_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (16)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta1_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (48)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                                                ; Lvar r4_17.(gv) ] __shuffle8 [:: Pvar r0_18
                                                                    ; Pvar r4_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r1_18.(gv)
                                                                ; Lvar r5_17.(gv) ] __shuffle8 [:: Pvar r1_18
                                                                    ; Pvar r5_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r2_15.(gv)
                                                                ; Lvar r6_17.(gv) ] __shuffle8 [:: Pvar r2_15
                                                                    ; Pvar r6_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r3_18.(gv)
                                                                ; Lvar r7_2.(gv) ] __shuffle8 [:: Pvar r3_18
                                                                    ; Pvar r7_2 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                                                ; Lvar r4_17.(gv)
                                                                ; Lvar r1_18.(gv)
                                                                ; Lvar r5_17.(gv)
                                                                ; Lvar r2_15.(gv)
                                                                ; Lvar r6_17.(gv)
                                                                ; Lvar r3_18.(gv)
                                                                ; Lvar r7_2.(gv) ] __butterfly64x [:: Pvar r0_18
                                                                    ; Pvar r4_17
                                                                    ; Pvar r1_18
                                                                    ; Pvar r5_17
                                                                    ; Pvar r2_15
                                                                    ; Pvar r6_17
                                                                    ; Pvar r3_18
                                                                    ; Pvar r7_2
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar qx16_11 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta0_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (80)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta1_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (112)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                                                ; Lvar r2_15.(gv) ] __shuffle4 [:: Pvar r0_18
                                                                    ; Pvar r2_15 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r4_17.(gv)
                                                                ; Lvar r6_17.(gv) ] __shuffle4 [:: Pvar r4_17
                                                                    ; Pvar r6_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r1_18.(gv)
                                                                ; Lvar r3_18.(gv) ] __shuffle4 [:: Pvar r1_18
                                                                    ; Pvar r3_18 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r5_17.(gv)
                                                                ; Lvar r7_2.(gv) ] __shuffle4 [:: Pvar r5_17
                                                                    ; Pvar r7_2 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                                                ; Lvar r2_15.(gv)
                                                                ; Lvar r4_17.(gv)
                                                                ; Lvar r6_17.(gv)
                                                                ; Lvar r1_18.(gv)
                                                                ; Lvar r3_18.(gv)
                                                                ; Lvar r5_17.(gv)
                                                                ; Lvar r7_2.(gv) ] __butterfly64x [:: Pvar r0_18
                                                                    ; Pvar r2_15
                                                                    ; Pvar r4_17
                                                                    ; Pvar r6_17
                                                                    ; Pvar r1_18
                                                                    ; Pvar r3_18
                                                                    ; Pvar r5_17
                                                                    ; Pvar r7_2
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar qx16_11 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta0_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (144)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta1_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (176)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                                                ; Lvar r1_18.(gv) ] __shuffle2 [:: Pvar r0_18
                                                                    ; Pvar r1_18 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r2_15.(gv)
                                                                ; Lvar r3_18.(gv) ] __shuffle2 [:: Pvar r2_15
                                                                    ; Pvar r3_18 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r4_17.(gv)
                                                                ; Lvar r5_17.(gv) ] __shuffle2 [:: Pvar r4_17
                                                                    ; Pvar r5_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r6_17.(gv)
                                                                ; Lvar r7_2.(gv) ] __shuffle2 [:: Pvar r6_17
                                                                    ; Pvar r7_2 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                                                ; Lvar r1_18.(gv)
                                                                ; Lvar r2_15.(gv)
                                                                ; Lvar r3_18.(gv)
                                                                ; Lvar r4_17.(gv)
                                                                ; Lvar r5_17.(gv)
                                                                ; Lvar r6_17.(gv)
                                                                ; Lvar r7_2.(gv) ] __butterfly64x [:: Pvar r0_18
                                                                    ; Pvar r1_18
                                                                    ; Pvar r2_15
                                                                    ; Pvar r3_18
                                                                    ; Pvar r4_17
                                                                    ; Pvar r5_17
                                                                    ; Pvar r6_17
                                                                    ; Pvar r7_2
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar qx16_11 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta0_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (208)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta1_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (240)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                                                ; Lvar r4_17.(gv) ] __shuffle1 [:: Pvar r0_18
                                                                    ; Pvar r4_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r1_18.(gv)
                                                                ; Lvar r5_17.(gv) ] __shuffle1 [:: Pvar r1_18
                                                                    ; Pvar r5_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r2_15.(gv)
                                                                ; Lvar r6_17.(gv) ] __shuffle1 [:: Pvar r2_15
                                                                    ; Pvar r6_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r3_18.(gv)
                                                                ; Lvar r7_2.(gv) ] __shuffle1 [:: Pvar r3_18
                                                                    ; Pvar r7_2 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                                                ; Lvar r4_17.(gv)
                                                                ; Lvar r1_18.(gv)
                                                                ; Lvar r5_17.(gv)
                                                                ; Lvar r2_15.(gv)
                                                                ; Lvar r6_17.(gv)
                                                                ; Lvar r3_18.(gv)
                                                                ; Lvar r7_2.(gv) ] __butterfly64x [:: Pvar r0_18
                                                                    ; Pvar r4_17
                                                                    ; Pvar r1_18
                                                                    ; Pvar r5_17
                                                                    ; Pvar r2_15
                                                                    ; Pvar r6_17
                                                                    ; Pvar r3_18
                                                                    ; Pvar r7_2
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar qx16_11 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta0_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (272)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta2_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (304)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta1_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (336)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta3_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (368)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_80)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv)
                                                                ; Lvar r4_17.(gv)
                                                                ; Lvar r2_15.(gv)
                                                                ; Lvar r6_17.(gv)
                                                                ; Lvar r1_18.(gv)
                                                                ; Lvar r5_17.(gv)
                                                                ; Lvar r3_18.(gv)
                                                                ; Lvar r7_2.(gv) ] __butterfly64x [:: Pvar r0_18
                                                                    ; Pvar r4_17
                                                                    ; Pvar r2_15
                                                                    ; Pvar r6_17
                                                                    ; Pvar r1_18
                                                                    ; Pvar r5_17
                                                                    ; Pvar r3_18
                                                                    ; Pvar r7_2
                                                                    ; Pvar zeta0_0
                                                                    ; Pvar zeta1_0
                                                                    ; Pvar zeta2_0
                                                                    ; Pvar zeta3_0
                                                                    ; Pvar qx16_11 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar vx16_1.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jvx16 (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_18.(gv) ] __red16x [:: Pvar r0_18
                                                                    ; Pvar qx16_11
                                                                    ; Pvar vx16_1 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r4_17.(gv) ] __red16x [:: Pvar r4_17
                                                                    ; Pvar qx16_11
                                                                    ; Pvar vx16_1 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r2_15.(gv) ] __red16x [:: Pvar r2_15
                                                                    ; Pvar qx16_11
                                                                    ; Pvar vx16_1 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r6_17.(gv) ] __red16x [:: Pvar r6_17
                                                                    ; Pvar qx16_11
                                                                    ; Pvar vx16_1 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r1_18.(gv) ] __red16x [:: Pvar r1_18
                                                                    ; Pvar qx16_11
                                                                    ; Pvar vx16_1 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r5_17.(gv) ] __red16x [:: Pvar r5_17
                                                                    ; Pvar qx16_11
                                                                    ; Pvar vx16_1 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r3_18.(gv) ] __red16x [:: Pvar r3_18
                                                                    ; Pvar qx16_11
                                                                    ; Pvar vx16_1 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r7_2.(gv) ] __red16x [:: Pvar r7_2
                                                                    ; Pvar qx16_11
                                                                    ; Pvar vx16_1 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))) AT_none (aword U256) (Pvar r0_18))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))) AT_none (aword U256) (Pvar r4_17))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))) AT_none (aword U256) (Pvar r1_18))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))) AT_none (aword U256) (Pvar r5_17))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))) AT_none (aword U256) (Pvar r2_15))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))) AT_none (aword U256) (Pvar r6_17))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))) AT_none (aword U256) (Pvar r3_18))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_10.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_80)))) AT_none (aword U256) (Pvar r7_2)) ]) ].

Definition fd__poly_ntt : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__poly_ntt;
    f_params := args__poly_ntt;
    f_body := body__poly_ntt;
    f_tyout := tyout__poly_ntt;
    f_res := res__poly_ntt;
    f_extra := tt;
  |}.

End IDO.
