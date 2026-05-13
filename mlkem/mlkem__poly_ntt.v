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

(* _poly_ntt *)
(* Local variables *)
Definition rp_14029 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14029).
Definition qx16_14030 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14030).
Definition zeta0_14031 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14031).
Definition zeta1_14032 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14032).
Definition r0_14033 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14033).
Definition r1_14034 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14034).
Definition r2_14035 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14035).
Definition r3_14036 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14036).
Definition r4_14037 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14037).
Definition r5_14038 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14038).
Definition r6_14039 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14039).
Definition r7_14040 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14040).
Definition i_14041 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14041).
Definition zeta2_14042 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14042).
Definition zeta3_14043 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14043).
Definition vx16_14044 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14044).

(* Signature *)
Definition tyin__poly_ntt : seq atype := [:: aarr U16 256 ].
Definition args__poly_ntt : seq var_i := [:: rp_14029.(gv) ].
Definition tyout__poly_ntt : seq atype := [:: aarr U16 256 ].
Definition res__poly_ntt : seq var_i := [:: rp_14029.(gv) ].

(* Body *)
Definition body__poly_ntt : cmd :=
  [:: cassgn (Lvar qx16_14030.(gv)) (aword U256) (Pget Aligned AAscale U256 jqx16 (Pconst (0)%Z))
    ; copn [:: Lvar zeta0_14031.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Aligned AAscale U32 jzetas_exp (Pconst (0)%Z) ]
    ; copn [:: Lvar zeta1_14032.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Aligned AAscale U32 jzetas_exp (Pconst (1)%Z) ]
    ; cassgn (Lvar r0_14033.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)))
    ; cassgn (Lvar r1_14034.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)))
    ; cassgn (Lvar r2_14035.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)))
    ; cassgn (Lvar r3_14036.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)))
    ; cassgn (Lvar r4_14037.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z)))
    ; cassgn (Lvar r5_14038.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z)))
    ; cassgn (Lvar r6_14039.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z)))
    ; cassgn (Lvar r7_14040.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z)))
    ; ccall [:: Lvar r0_14033.(gv)
              ; Lvar r1_14034.(gv)
              ; Lvar r2_14035.(gv)
              ; Lvar r3_14036.(gv)
              ; Lvar r4_14037.(gv)
              ; Lvar r5_14038.(gv)
              ; Lvar r6_14039.(gv)
              ; Lvar r7_14040.(gv) ] __butterfly64x [:: Pvar r0_14033
                                                      ; Pvar r1_14034
                                                      ; Pvar r2_14035
                                                      ; Pvar r3_14036
                                                      ; Pvar r4_14037
                                                      ; Pvar r5_14038
                                                      ; Pvar r6_14039
                                                      ; Pvar r7_14040
                                                      ; Pvar zeta0_14031
                                                      ; Pvar zeta0_14031
                                                      ; Pvar zeta1_14032
                                                      ; Pvar zeta1_14032
                                                      ; Pvar qx16_14030 ]
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))) (aword U256) (Pvar r0_14033)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))) (aword U256) (Pvar r1_14034)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))) (aword U256) (Pvar r2_14035)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))) (aword U256) (Pvar r3_14036)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))) (aword U256) (Pvar r4_14037)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))) (aword U256) (Pvar r5_14038)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))) (aword U256) (Pvar r6_14039)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))) (aword U256) (Pvar r7_14040)
    ; cassgn (Lvar r0_14033.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)))
    ; cassgn (Lvar r1_14034.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)))
    ; cassgn (Lvar r2_14035.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)))
    ; cassgn (Lvar r3_14036.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)))
    ; cassgn (Lvar r4_14037.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z)))
    ; cassgn (Lvar r5_14038.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z)))
    ; cassgn (Lvar r6_14039.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z)))
    ; cassgn (Lvar r7_14040.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z)))
    ; ccall [:: Lvar r0_14033.(gv)
              ; Lvar r1_14034.(gv)
              ; Lvar r2_14035.(gv)
              ; Lvar r3_14036.(gv)
              ; Lvar r4_14037.(gv)
              ; Lvar r5_14038.(gv)
              ; Lvar r6_14039.(gv)
              ; Lvar r7_14040.(gv) ] __butterfly64x [:: Pvar r0_14033
                                                      ; Pvar r1_14034
                                                      ; Pvar r2_14035
                                                      ; Pvar r3_14036
                                                      ; Pvar r4_14037
                                                      ; Pvar r5_14038
                                                      ; Pvar r6_14039
                                                      ; Pvar r7_14040
                                                      ; Pvar zeta0_14031
                                                      ; Pvar zeta0_14031
                                                      ; Pvar zeta1_14032
                                                      ; Pvar zeta1_14032
                                                      ; Pvar qx16_14030 ]
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))) (aword U256) (Pvar r4_14037)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))) (aword U256) (Pvar r5_14038)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))) (aword U256) (Pvar r6_14039)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))) (aword U256) (Pvar r7_14040)
    ; cfor
        (i_14041.(gv))
        (UpTo, Pconst (0)%Z, Pconst (2)%Z)
        [:: copn [:: Lvar zeta0_14031.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (8)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))) ]
          ; copn [:: Lvar zeta1_14032.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (12)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))) ]
          ; cif
              (Papp2 (Oeq (Op_int)) (Pvar i_14041) (Pconst (0)%Z))
              [:: cassgn (Lvar r4_14037.(gv)) (aword U256) (Pvar r0_14033)
                ; cassgn (Lvar r5_14038.(gv)) (aword U256) (Pvar r1_14034)
                ; cassgn (Lvar r6_14039.(gv)) (aword U256) (Pvar r2_14035)
                ; cassgn (Lvar r7_14040.(gv)) (aword U256) (Pvar r3_14036) ]
              [:: cassgn (Lvar r4_14037.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041))))
                ; cassgn (Lvar r5_14038.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041))))
                ; cassgn (Lvar r6_14039.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041))))
                ; cassgn (Lvar r7_14040.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041)))) ]
          ; cassgn (Lvar r0_14033.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041))))
          ; cassgn (Lvar r1_14034.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041))))
          ; cassgn (Lvar r2_14035.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041))))
          ; cassgn (Lvar r3_14036.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14029 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041))))
          ; ccall [:: Lvar r0_14033.(gv)
                    ; Lvar r1_14034.(gv)
                    ; Lvar r2_14035.(gv)
                    ; Lvar r3_14036.(gv)
                    ; Lvar r4_14037.(gv)
                    ; Lvar r5_14038.(gv)
                    ; Lvar r6_14039.(gv)
                    ; Lvar r7_14040.(gv) ] __butterfly64x [:: Pvar r0_14033
                                                            ; Pvar r1_14034
                                                            ; Pvar r2_14035
                                                            ; Pvar r3_14036
                                                            ; Pvar r4_14037
                                                            ; Pvar r5_14038
                                                            ; Pvar r6_14039
                                                            ; Pvar r7_14040
                                                            ; Pvar zeta0_14031
                                                            ; Pvar zeta0_14031
                                                            ; Pvar zeta1_14032
                                                            ; Pvar zeta1_14032
                                                            ; Pvar qx16_14030 ]
          ; cassgn (Lvar zeta0_14031.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (16)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; cassgn (Lvar zeta1_14032.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (48)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; ccall [:: Lvar r0_14033.(gv); Lvar r4_14037.(gv) ] __shuffle8 [:: Pvar r0_14033
                                                                    ; Pvar r4_14037 ]
          ; ccall [:: Lvar r1_14034.(gv); Lvar r5_14038.(gv) ] __shuffle8 [:: Pvar r1_14034
                                                                    ; Pvar r5_14038 ]
          ; ccall [:: Lvar r2_14035.(gv); Lvar r6_14039.(gv) ] __shuffle8 [:: Pvar r2_14035
                                                                    ; Pvar r6_14039 ]
          ; ccall [:: Lvar r3_14036.(gv); Lvar r7_14040.(gv) ] __shuffle8 [:: Pvar r3_14036
                                                                    ; Pvar r7_14040 ]
          ; ccall [:: Lvar r0_14033.(gv)
                    ; Lvar r4_14037.(gv)
                    ; Lvar r1_14034.(gv)
                    ; Lvar r5_14038.(gv)
                    ; Lvar r2_14035.(gv)
                    ; Lvar r6_14039.(gv)
                    ; Lvar r3_14036.(gv)
                    ; Lvar r7_14040.(gv) ] __butterfly64x [:: Pvar r0_14033
                                                            ; Pvar r4_14037
                                                            ; Pvar r1_14034
                                                            ; Pvar r5_14038
                                                            ; Pvar r2_14035
                                                            ; Pvar r6_14039
                                                            ; Pvar r3_14036
                                                            ; Pvar r7_14040
                                                            ; Pvar zeta0_14031
                                                            ; Pvar zeta0_14031
                                                            ; Pvar zeta1_14032
                                                            ; Pvar zeta1_14032
                                                            ; Pvar qx16_14030 ]
          ; cassgn (Lvar zeta0_14031.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (80)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; cassgn (Lvar zeta1_14032.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (112)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; ccall [:: Lvar r0_14033.(gv); Lvar r2_14035.(gv) ] __shuffle4 [:: Pvar r0_14033
                                                                    ; Pvar r2_14035 ]
          ; ccall [:: Lvar r4_14037.(gv); Lvar r6_14039.(gv) ] __shuffle4 [:: Pvar r4_14037
                                                                    ; Pvar r6_14039 ]
          ; ccall [:: Lvar r1_14034.(gv); Lvar r3_14036.(gv) ] __shuffle4 [:: Pvar r1_14034
                                                                    ; Pvar r3_14036 ]
          ; ccall [:: Lvar r5_14038.(gv); Lvar r7_14040.(gv) ] __shuffle4 [:: Pvar r5_14038
                                                                    ; Pvar r7_14040 ]
          ; ccall [:: Lvar r0_14033.(gv)
                    ; Lvar r2_14035.(gv)
                    ; Lvar r4_14037.(gv)
                    ; Lvar r6_14039.(gv)
                    ; Lvar r1_14034.(gv)
                    ; Lvar r3_14036.(gv)
                    ; Lvar r5_14038.(gv)
                    ; Lvar r7_14040.(gv) ] __butterfly64x [:: Pvar r0_14033
                                                            ; Pvar r2_14035
                                                            ; Pvar r4_14037
                                                            ; Pvar r6_14039
                                                            ; Pvar r1_14034
                                                            ; Pvar r3_14036
                                                            ; Pvar r5_14038
                                                            ; Pvar r7_14040
                                                            ; Pvar zeta0_14031
                                                            ; Pvar zeta0_14031
                                                            ; Pvar zeta1_14032
                                                            ; Pvar zeta1_14032
                                                            ; Pvar qx16_14030 ]
          ; cassgn (Lvar zeta0_14031.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (144)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; cassgn (Lvar zeta1_14032.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (176)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; ccall [:: Lvar r0_14033.(gv); Lvar r1_14034.(gv) ] __shuffle2 [:: Pvar r0_14033
                                                                    ; Pvar r1_14034 ]
          ; ccall [:: Lvar r2_14035.(gv); Lvar r3_14036.(gv) ] __shuffle2 [:: Pvar r2_14035
                                                                    ; Pvar r3_14036 ]
          ; ccall [:: Lvar r4_14037.(gv); Lvar r5_14038.(gv) ] __shuffle2 [:: Pvar r4_14037
                                                                    ; Pvar r5_14038 ]
          ; ccall [:: Lvar r6_14039.(gv); Lvar r7_14040.(gv) ] __shuffle2 [:: Pvar r6_14039
                                                                    ; Pvar r7_14040 ]
          ; ccall [:: Lvar r0_14033.(gv)
                    ; Lvar r1_14034.(gv)
                    ; Lvar r2_14035.(gv)
                    ; Lvar r3_14036.(gv)
                    ; Lvar r4_14037.(gv)
                    ; Lvar r5_14038.(gv)
                    ; Lvar r6_14039.(gv)
                    ; Lvar r7_14040.(gv) ] __butterfly64x [:: Pvar r0_14033
                                                            ; Pvar r1_14034
                                                            ; Pvar r2_14035
                                                            ; Pvar r3_14036
                                                            ; Pvar r4_14037
                                                            ; Pvar r5_14038
                                                            ; Pvar r6_14039
                                                            ; Pvar r7_14040
                                                            ; Pvar zeta0_14031
                                                            ; Pvar zeta0_14031
                                                            ; Pvar zeta1_14032
                                                            ; Pvar zeta1_14032
                                                            ; Pvar qx16_14030 ]
          ; cassgn (Lvar zeta0_14031.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (208)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; cassgn (Lvar zeta1_14032.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (240)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; ccall [:: Lvar r0_14033.(gv); Lvar r4_14037.(gv) ] __shuffle1 [:: Pvar r0_14033
                                                                    ; Pvar r4_14037 ]
          ; ccall [:: Lvar r1_14034.(gv); Lvar r5_14038.(gv) ] __shuffle1 [:: Pvar r1_14034
                                                                    ; Pvar r5_14038 ]
          ; ccall [:: Lvar r2_14035.(gv); Lvar r6_14039.(gv) ] __shuffle1 [:: Pvar r2_14035
                                                                    ; Pvar r6_14039 ]
          ; ccall [:: Lvar r3_14036.(gv); Lvar r7_14040.(gv) ] __shuffle1 [:: Pvar r3_14036
                                                                    ; Pvar r7_14040 ]
          ; ccall [:: Lvar r0_14033.(gv)
                    ; Lvar r4_14037.(gv)
                    ; Lvar r1_14034.(gv)
                    ; Lvar r5_14038.(gv)
                    ; Lvar r2_14035.(gv)
                    ; Lvar r6_14039.(gv)
                    ; Lvar r3_14036.(gv)
                    ; Lvar r7_14040.(gv) ] __butterfly64x [:: Pvar r0_14033
                                                            ; Pvar r4_14037
                                                            ; Pvar r1_14034
                                                            ; Pvar r5_14038
                                                            ; Pvar r2_14035
                                                            ; Pvar r6_14039
                                                            ; Pvar r3_14036
                                                            ; Pvar r7_14040
                                                            ; Pvar zeta0_14031
                                                            ; Pvar zeta0_14031
                                                            ; Pvar zeta1_14032
                                                            ; Pvar zeta1_14032
                                                            ; Pvar qx16_14030 ]
          ; cassgn (Lvar zeta0_14031.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (272)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; cassgn (Lvar zeta2_14042.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (304)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; cassgn (Lvar zeta1_14032.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (336)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; cassgn (Lvar zeta3_14043.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Papp2 (Oadd (Op_int)) (Pconst (368)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14041))))
          ; ccall [:: Lvar r0_14033.(gv)
                    ; Lvar r4_14037.(gv)
                    ; Lvar r2_14035.(gv)
                    ; Lvar r6_14039.(gv)
                    ; Lvar r1_14034.(gv)
                    ; Lvar r5_14038.(gv)
                    ; Lvar r3_14036.(gv)
                    ; Lvar r7_14040.(gv) ] __butterfly64x [:: Pvar r0_14033
                                                            ; Pvar r4_14037
                                                            ; Pvar r2_14035
                                                            ; Pvar r6_14039
                                                            ; Pvar r1_14034
                                                            ; Pvar r5_14038
                                                            ; Pvar r3_14036
                                                            ; Pvar r7_14040
                                                            ; Pvar zeta0_14031
                                                            ; Pvar zeta1_14032
                                                            ; Pvar zeta2_14042
                                                            ; Pvar zeta3_14043
                                                            ; Pvar qx16_14030 ]
          ; cassgn (Lvar vx16_14044.(gv)) (aword U256) (Pget Aligned AAscale U256 jvx16 (Pconst (0)%Z))
          ; ccall [:: Lvar r0_14033.(gv) ] __red16x [:: Pvar r0_14033
                                                      ; Pvar qx16_14030
                                                      ; Pvar vx16_14044 ]
          ; ccall [:: Lvar r4_14037.(gv) ] __red16x [:: Pvar r4_14037
                                                      ; Pvar qx16_14030
                                                      ; Pvar vx16_14044 ]
          ; ccall [:: Lvar r2_14035.(gv) ] __red16x [:: Pvar r2_14035
                                                      ; Pvar qx16_14030
                                                      ; Pvar vx16_14044 ]
          ; ccall [:: Lvar r6_14039.(gv) ] __red16x [:: Pvar r6_14039
                                                      ; Pvar qx16_14030
                                                      ; Pvar vx16_14044 ]
          ; ccall [:: Lvar r1_14034.(gv) ] __red16x [:: Pvar r1_14034
                                                      ; Pvar qx16_14030
                                                      ; Pvar vx16_14044 ]
          ; ccall [:: Lvar r5_14038.(gv) ] __red16x [:: Pvar r5_14038
                                                      ; Pvar qx16_14030
                                                      ; Pvar vx16_14044 ]
          ; ccall [:: Lvar r3_14036.(gv) ] __red16x [:: Pvar r3_14036
                                                      ; Pvar qx16_14030
                                                      ; Pvar vx16_14044 ]
          ; ccall [:: Lvar r7_14040.(gv) ] __red16x [:: Pvar r7_14040
                                                      ; Pvar qx16_14030
                                                      ; Pvar vx16_14044 ]
          ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041)))) (aword U256) (Pvar r0_14033)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041)))) (aword U256) (Pvar r4_14037)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041)))) (aword U256) (Pvar r1_14034)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041)))) (aword U256) (Pvar r5_14038)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041)))) (aword U256) (Pvar r2_14035)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041)))) (aword U256) (Pvar r6_14039)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041)))) (aword U256) (Pvar r3_14036)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14029.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14041)))) (aword U256) (Pvar r7_14040) ] ].

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
