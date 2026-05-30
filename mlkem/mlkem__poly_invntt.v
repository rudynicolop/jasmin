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

(* _poly_invntt *)
(* Local variables *)
Definition rp_9 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14066).
Definition qx16_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14067).
Definition i_79 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14068).
Definition zeta0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14069).
Definition zeta1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14070).
Definition zeta2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14071).
Definition zeta3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14072).
Definition r0_17 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14073).
Definition r1_17 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14074).
Definition r2_14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14075).
Definition r3_17 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14076).
Definition r4_16 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14077).
Definition r5_16 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14078).
Definition r6_16 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14079).
Definition r7_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14080).
Definition vx16_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14081).
Definition flox16 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14082).
Definition fhix16 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14083).

(* Signature *)
Definition tyin__poly_invntt : seq atype := [:: aarr U16 256 ].
Definition args__poly_invntt : seq var_i := [:: rp_9.(gv) ].
Definition tyout__poly_invntt : seq atype := [:: aarr U16 256 ].
Definition res__poly_invntt : seq var_i := [:: rp_9.(gv) ].

(* Body *)
Definition body__poly_invntt : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar qx16_9.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jqx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cfor
                              (i_79.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (2)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar zeta0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (0)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta1.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (64)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta2.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (32)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta3.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (96)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r0_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r1_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_14.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r3_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r4_16.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r5_16.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r6_16.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r7_1.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv)
                                                                ; Lvar r1_17.(gv)
                                                                ; Lvar r4_16.(gv)
                                                                ; Lvar r5_16.(gv)
                                                                ; Lvar r2_14.(gv)
                                                                ; Lvar r3_17.(gv)
                                                                ; Lvar r6_16.(gv)
                                                                ; Lvar r7_1.(gv) ] __invntt___butterfly64x [:: Pvar r0_17
                                                                    ; Pvar r1_17
                                                                    ; Pvar r4_16
                                                                    ; Pvar r5_16
                                                                    ; Pvar r2_14
                                                                    ; Pvar r3_17
                                                                    ; Pvar r6_16
                                                                    ; Pvar r7_1
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta2
                                                                    ; Pvar zeta3
                                                                    ; Pvar qx16_9 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar vx16_0.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jvx16 (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (128)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta1.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (160)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv) ] __red16x [:: Pvar r0_17
                                                                    ; Pvar qx16_9
                                                                    ; Pvar vx16_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r1_17.(gv) ] __red16x [:: Pvar r1_17
                                                                    ; Pvar qx16_9
                                                                    ; Pvar vx16_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r4_16.(gv) ] __red16x [:: Pvar r4_16
                                                                    ; Pvar qx16_9
                                                                    ; Pvar vx16_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r5_16.(gv) ] __red16x [:: Pvar r5_16
                                                                    ; Pvar qx16_9
                                                                    ; Pvar vx16_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv)
                                                                ; Lvar r1_17.(gv)
                                                                ; Lvar r2_14.(gv)
                                                                ; Lvar r3_17.(gv)
                                                                ; Lvar r4_16.(gv)
                                                                ; Lvar r5_16.(gv)
                                                                ; Lvar r6_16.(gv)
                                                                ; Lvar r7_1.(gv) ] __invntt___butterfly64x [:: Pvar r0_17
                                                                    ; Pvar r1_17
                                                                    ; Pvar r2_14
                                                                    ; Pvar r3_17
                                                                    ; Pvar r4_16
                                                                    ; Pvar r5_16
                                                                    ; Pvar r6_16
                                                                    ; Pvar r7_1
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_9 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv)
                                                                ; Lvar r1_17.(gv) ] __shuffle1 [:: Pvar r0_17
                                                                    ; Pvar r1_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r2_14.(gv)
                                                                ; Lvar r3_17.(gv) ] __shuffle1 [:: Pvar r2_14
                                                                    ; Pvar r3_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r4_16.(gv)
                                                                ; Lvar r5_16.(gv) ] __shuffle1 [:: Pvar r4_16
                                                                    ; Pvar r5_16 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r6_16.(gv)
                                                                ; Lvar r7_1.(gv) ] __shuffle1 [:: Pvar r6_16
                                                                    ; Pvar r7_1 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (192)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta1.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (224)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv)
                                                                ; Lvar r2_14.(gv)
                                                                ; Lvar r4_16.(gv)
                                                                ; Lvar r6_16.(gv)
                                                                ; Lvar r1_17.(gv)
                                                                ; Lvar r3_17.(gv)
                                                                ; Lvar r5_16.(gv)
                                                                ; Lvar r7_1.(gv) ] __invntt___butterfly64x [:: Pvar r0_17
                                                                    ; Pvar r2_14
                                                                    ; Pvar r4_16
                                                                    ; Pvar r6_16
                                                                    ; Pvar r1_17
                                                                    ; Pvar r3_17
                                                                    ; Pvar r5_16
                                                                    ; Pvar r7_1
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_9 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv) ] __red16x [:: Pvar r0_17
                                                                    ; Pvar qx16_9
                                                                    ; Pvar vx16_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv)
                                                                ; Lvar r2_14.(gv) ] __shuffle2 [:: Pvar r0_17
                                                                    ; Pvar r2_14 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r4_16.(gv)
                                                                ; Lvar r6_16.(gv) ] __shuffle2 [:: Pvar r4_16
                                                                    ; Pvar r6_16 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r1_17.(gv)
                                                                ; Lvar r3_17.(gv) ] __shuffle2 [:: Pvar r1_17
                                                                    ; Pvar r3_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r5_16.(gv)
                                                                ; Lvar r7_1.(gv) ] __shuffle2 [:: Pvar r5_16
                                                                    ; Pvar r7_1 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (256)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta1.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (288)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv)
                                                                ; Lvar r4_16.(gv)
                                                                ; Lvar r1_17.(gv)
                                                                ; Lvar r5_16.(gv)
                                                                ; Lvar r2_14.(gv)
                                                                ; Lvar r6_16.(gv)
                                                                ; Lvar r3_17.(gv)
                                                                ; Lvar r7_1.(gv) ] __invntt___butterfly64x [:: Pvar r0_17
                                                                    ; Pvar r4_16
                                                                    ; Pvar r1_17
                                                                    ; Pvar r5_16
                                                                    ; Pvar r2_14
                                                                    ; Pvar r6_16
                                                                    ; Pvar r3_17
                                                                    ; Pvar r7_1
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_9 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv) ] __red16x [:: Pvar r0_17
                                                                    ; Pvar qx16_9
                                                                    ; Pvar vx16_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv)
                                                                ; Lvar r4_16.(gv) ] __shuffle4 [:: Pvar r0_17
                                                                    ; Pvar r4_16 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r1_17.(gv)
                                                                ; Lvar r5_16.(gv) ] __shuffle4 [:: Pvar r1_17
                                                                    ; Pvar r5_16 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r2_14.(gv)
                                                                ; Lvar r6_16.(gv) ] __shuffle4 [:: Pvar r2_14
                                                                    ; Pvar r6_16 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r3_17.(gv)
                                                                ; Lvar r7_1.(gv) ] __shuffle4 [:: Pvar r3_17
                                                                    ; Pvar r7_1 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (320)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar zeta1.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (352)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv)
                                                                ; Lvar r1_17.(gv)
                                                                ; Lvar r2_14.(gv)
                                                                ; Lvar r3_17.(gv)
                                                                ; Lvar r4_16.(gv)
                                                                ; Lvar r5_16.(gv)
                                                                ; Lvar r6_16.(gv)
                                                                ; Lvar r7_1.(gv) ] __invntt___butterfly64x [:: Pvar r0_17
                                                                    ; Pvar r1_17
                                                                    ; Pvar r2_14
                                                                    ; Pvar r3_17
                                                                    ; Pvar r4_16
                                                                    ; Pvar r5_16
                                                                    ; Pvar r6_16
                                                                    ; Pvar r7_1
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_9 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv) ] __red16x [:: Pvar r0_17
                                                                    ; Pvar qx16_9
                                                                    ; Pvar vx16_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv)
                                                                ; Lvar r1_17.(gv) ] __shuffle8 [:: Pvar r0_17
                                                                    ; Pvar r1_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r2_14.(gv)
                                                                ; Lvar r3_17.(gv) ] __shuffle8 [:: Pvar r2_14
                                                                    ; Pvar r3_17 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r4_16.(gv)
                                                                ; Lvar r5_16.(gv) ] __shuffle8 [:: Pvar r4_16
                                                                    ; Pvar r5_16 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r6_16.(gv)
                                                                ; Lvar r7_1.(gv) ] __shuffle8 [:: Pvar r6_16
                                                                    ; Pvar r7_1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar zeta0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (384)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79))) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar zeta1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (388)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_79))) ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv)
                                                                ; Lvar r2_14.(gv)
                                                                ; Lvar r4_16.(gv)
                                                                ; Lvar r6_16.(gv)
                                                                ; Lvar r1_17.(gv)
                                                                ; Lvar r3_17.(gv)
                                                                ; Lvar r5_16.(gv)
                                                                ; Lvar r7_1.(gv) ] __invntt___butterfly64x [:: Pvar r0_17
                                                                    ; Pvar r2_14
                                                                    ; Pvar r4_16
                                                                    ; Pvar r6_16
                                                                    ; Pvar r1_17
                                                                    ; Pvar r3_17
                                                                    ; Pvar r5_16
                                                                    ; Pvar r7_1
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_9 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv) ] __red16x [:: Pvar r0_17
                                                                    ; Pvar qx16_9
                                                                    ; Pvar vx16_0 ])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oeq (Op_int)) (Pvar i_79) (Pconst (0)%Z))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r0_17))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r2_14))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r4_16))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r6_16)) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r1_17))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r3_17))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r5_16))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r7_1)) ])
    ; MkI dummy_instr_info (Copn [:: Lvar zeta0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_inv_exp (Pconst (784)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar zeta1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_inv_exp (Pconst (788)%Z) ])
    ; MkI dummy_instr_info (Cfor
                              (i_79.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (2)%Z)
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Oeq (Op_int)) (Pvar i_79) (Pconst (0)%Z))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar r7_1.(gv)) AT_none (aword U256) (Pvar r6_16))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r6_16.(gv)) AT_none (aword U256) (Pvar r4_16))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r5_16.(gv)) AT_none (aword U256) (Pvar r2_14))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r4_16.(gv)) AT_none (aword U256) (Pvar r0_17)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar r4_16.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r5_16.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r6_16.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar r7_1.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79))))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar r0_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r1_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_14.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar r3_17.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_9 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv)
                                                                ; Lvar r1_17.(gv)
                                                                ; Lvar r2_14.(gv)
                                                                ; Lvar r3_17.(gv)
                                                                ; Lvar r4_16.(gv)
                                                                ; Lvar r5_16.(gv)
                                                                ; Lvar r6_16.(gv)
                                                                ; Lvar r7_1.(gv) ] __invntt___butterfly64x [:: Pvar r0_17
                                                                    ; Pvar r1_17
                                                                    ; Pvar r2_14
                                                                    ; Pvar r3_17
                                                                    ; Pvar r4_16
                                                                    ; Pvar r5_16
                                                                    ; Pvar r6_16
                                                                    ; Pvar r7_1
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_9 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar flox16.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jflox16 (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cassgn (Lvar fhix16.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jfhix16 (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r4_16))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r5_16))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r6_16))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r7_1))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r0_17.(gv) ] __fqmulprecomp16x [:: Pvar r0_17
                                                                    ; Pvar flox16
                                                                    ; Pvar fhix16
                                                                    ; Pvar qx16_9 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r1_17.(gv) ] __fqmulprecomp16x [:: Pvar r1_17
                                                                    ; Pvar flox16
                                                                    ; Pvar fhix16
                                                                    ; Pvar qx16_9 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r2_14.(gv) ] __fqmulprecomp16x [:: Pvar r2_14
                                                                    ; Pvar flox16
                                                                    ; Pvar fhix16
                                                                    ; Pvar qx16_9 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar r3_17.(gv) ] __fqmulprecomp16x [:: Pvar r3_17
                                                                    ; Pvar flox16
                                                                    ; Pvar fhix16
                                                                    ; Pvar qx16_9 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r0_17))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r1_17))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r2_14))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_9.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_79)))) AT_none (aword U256) (Pvar r3_17)) ]) ].

Definition fd__poly_invntt : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__poly_invntt;
    f_params := args__poly_invntt;
    f_body := body__poly_invntt;
    f_tyout := tyout__poly_invntt;
    f_res := res__poly_invntt;
    f_extra := tt;
  |}.

End IDO.
