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

(* _poly_invntt *)
(* Local variables *)
Definition rp_14066 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14066).
Definition qx16_14067 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14067).
Definition i_14068 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14068).
Definition zeta0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14069).
Definition zeta1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14070).
Definition zeta2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14071).
Definition zeta3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14072).
Definition r0_14073 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14073).
Definition r1_14074 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14074).
Definition r2_14075 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14075).
Definition r3_14076 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14076).
Definition r4_14077 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14077).
Definition r5_14078 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14078).
Definition r6_14079 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14079).
Definition r7_14080 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14080).
Definition vx16_14081 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14081).
Definition flox16 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14082).
Definition fhix16 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14083).

(* Signature *)
Definition tyin__poly_invntt : seq atype := [:: aarr U16 256 ].
Definition args__poly_invntt : seq var_i := [:: rp_14066.(gv) ].
Definition tyout__poly_invntt : seq atype := [:: aarr U16 256 ].
Definition res__poly_invntt : seq var_i := [:: rp_14066.(gv) ].

(* Body *)
Definition body__poly_invntt : cmd :=
  [:: cassgn (Lvar qx16_14067.(gv)) (aword U256) (Pget Aligned AAscale U256 jqx16 (Pconst (0)%Z))
    ; cfor
        (i_14068.(gv))
        (UpTo, Pconst (0)%Z, Pconst (2)%Z)
        [:: cassgn (Lvar zeta0.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (0)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; cassgn (Lvar zeta1.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (64)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; cassgn (Lvar zeta2.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (32)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; cassgn (Lvar zeta3.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (96)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; cassgn (Lvar r0_14073.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068))))
          ; cassgn (Lvar r1_14074.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068))))
          ; cassgn (Lvar r2_14075.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068))))
          ; cassgn (Lvar r3_14076.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068))))
          ; cassgn (Lvar r4_14077.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068))))
          ; cassgn (Lvar r5_14078.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068))))
          ; cassgn (Lvar r6_14079.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068))))
          ; cassgn (Lvar r7_14080.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068))))
          ; ccall [:: Lvar r0_14073.(gv)
                    ; Lvar r1_14074.(gv)
                    ; Lvar r4_14077.(gv)
                    ; Lvar r5_14078.(gv)
                    ; Lvar r2_14075.(gv)
                    ; Lvar r3_14076.(gv)
                    ; Lvar r6_14079.(gv)
                    ; Lvar r7_14080.(gv) ] __invntt___butterfly64x [:: Pvar r0_14073
                                                                    ; Pvar r1_14074
                                                                    ; Pvar r4_14077
                                                                    ; Pvar r5_14078
                                                                    ; Pvar r2_14075
                                                                    ; Pvar r3_14076
                                                                    ; Pvar r6_14079
                                                                    ; Pvar r7_14080
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta2
                                                                    ; Pvar zeta3
                                                                    ; Pvar qx16_14067 ]
          ; cassgn (Lvar vx16_14081.(gv)) (aword U256) (Pget Aligned AAscale U256 jvx16 (Pconst (0)%Z))
          ; cassgn (Lvar zeta0.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (128)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; cassgn (Lvar zeta1.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (160)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; ccall [:: Lvar r0_14073.(gv) ] __red16x [:: Pvar r0_14073
                                                      ; Pvar qx16_14067
                                                      ; Pvar vx16_14081 ]
          ; ccall [:: Lvar r1_14074.(gv) ] __red16x [:: Pvar r1_14074
                                                      ; Pvar qx16_14067
                                                      ; Pvar vx16_14081 ]
          ; ccall [:: Lvar r4_14077.(gv) ] __red16x [:: Pvar r4_14077
                                                      ; Pvar qx16_14067
                                                      ; Pvar vx16_14081 ]
          ; ccall [:: Lvar r5_14078.(gv) ] __red16x [:: Pvar r5_14078
                                                      ; Pvar qx16_14067
                                                      ; Pvar vx16_14081 ]
          ; ccall [:: Lvar r0_14073.(gv)
                    ; Lvar r1_14074.(gv)
                    ; Lvar r2_14075.(gv)
                    ; Lvar r3_14076.(gv)
                    ; Lvar r4_14077.(gv)
                    ; Lvar r5_14078.(gv)
                    ; Lvar r6_14079.(gv)
                    ; Lvar r7_14080.(gv) ] __invntt___butterfly64x [:: Pvar r0_14073
                                                                    ; Pvar r1_14074
                                                                    ; Pvar r2_14075
                                                                    ; Pvar r3_14076
                                                                    ; Pvar r4_14077
                                                                    ; Pvar r5_14078
                                                                    ; Pvar r6_14079
                                                                    ; Pvar r7_14080
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_14067 ]
          ; ccall [:: Lvar r0_14073.(gv); Lvar r1_14074.(gv) ] __shuffle1 [:: Pvar r0_14073
                                                                    ; Pvar r1_14074 ]
          ; ccall [:: Lvar r2_14075.(gv); Lvar r3_14076.(gv) ] __shuffle1 [:: Pvar r2_14075
                                                                    ; Pvar r3_14076 ]
          ; ccall [:: Lvar r4_14077.(gv); Lvar r5_14078.(gv) ] __shuffle1 [:: Pvar r4_14077
                                                                    ; Pvar r5_14078 ]
          ; ccall [:: Lvar r6_14079.(gv); Lvar r7_14080.(gv) ] __shuffle1 [:: Pvar r6_14079
                                                                    ; Pvar r7_14080 ]
          ; cassgn (Lvar zeta0.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (192)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; cassgn (Lvar zeta1.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (224)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; ccall [:: Lvar r0_14073.(gv)
                    ; Lvar r2_14075.(gv)
                    ; Lvar r4_14077.(gv)
                    ; Lvar r6_14079.(gv)
                    ; Lvar r1_14074.(gv)
                    ; Lvar r3_14076.(gv)
                    ; Lvar r5_14078.(gv)
                    ; Lvar r7_14080.(gv) ] __invntt___butterfly64x [:: Pvar r0_14073
                                                                    ; Pvar r2_14075
                                                                    ; Pvar r4_14077
                                                                    ; Pvar r6_14079
                                                                    ; Pvar r1_14074
                                                                    ; Pvar r3_14076
                                                                    ; Pvar r5_14078
                                                                    ; Pvar r7_14080
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_14067 ]
          ; ccall [:: Lvar r0_14073.(gv) ] __red16x [:: Pvar r0_14073
                                                      ; Pvar qx16_14067
                                                      ; Pvar vx16_14081 ]
          ; ccall [:: Lvar r0_14073.(gv); Lvar r2_14075.(gv) ] __shuffle2 [:: Pvar r0_14073
                                                                    ; Pvar r2_14075 ]
          ; ccall [:: Lvar r4_14077.(gv); Lvar r6_14079.(gv) ] __shuffle2 [:: Pvar r4_14077
                                                                    ; Pvar r6_14079 ]
          ; ccall [:: Lvar r1_14074.(gv); Lvar r3_14076.(gv) ] __shuffle2 [:: Pvar r1_14074
                                                                    ; Pvar r3_14076 ]
          ; ccall [:: Lvar r5_14078.(gv); Lvar r7_14080.(gv) ] __shuffle2 [:: Pvar r5_14078
                                                                    ; Pvar r7_14080 ]
          ; cassgn (Lvar zeta0.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (256)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; cassgn (Lvar zeta1.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (288)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; ccall [:: Lvar r0_14073.(gv)
                    ; Lvar r4_14077.(gv)
                    ; Lvar r1_14074.(gv)
                    ; Lvar r5_14078.(gv)
                    ; Lvar r2_14075.(gv)
                    ; Lvar r6_14079.(gv)
                    ; Lvar r3_14076.(gv)
                    ; Lvar r7_14080.(gv) ] __invntt___butterfly64x [:: Pvar r0_14073
                                                                    ; Pvar r4_14077
                                                                    ; Pvar r1_14074
                                                                    ; Pvar r5_14078
                                                                    ; Pvar r2_14075
                                                                    ; Pvar r6_14079
                                                                    ; Pvar r3_14076
                                                                    ; Pvar r7_14080
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_14067 ]
          ; ccall [:: Lvar r0_14073.(gv) ] __red16x [:: Pvar r0_14073
                                                      ; Pvar qx16_14067
                                                      ; Pvar vx16_14081 ]
          ; ccall [:: Lvar r0_14073.(gv); Lvar r4_14077.(gv) ] __shuffle4 [:: Pvar r0_14073
                                                                    ; Pvar r4_14077 ]
          ; ccall [:: Lvar r1_14074.(gv); Lvar r5_14078.(gv) ] __shuffle4 [:: Pvar r1_14074
                                                                    ; Pvar r5_14078 ]
          ; ccall [:: Lvar r2_14075.(gv); Lvar r6_14079.(gv) ] __shuffle4 [:: Pvar r2_14075
                                                                    ; Pvar r6_14079 ]
          ; ccall [:: Lvar r3_14076.(gv); Lvar r7_14080.(gv) ] __shuffle4 [:: Pvar r3_14076
                                                                    ; Pvar r7_14080 ]
          ; cassgn (Lvar zeta0.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (320)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; cassgn (Lvar zeta1.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (352)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))))
          ; ccall [:: Lvar r0_14073.(gv)
                    ; Lvar r1_14074.(gv)
                    ; Lvar r2_14075.(gv)
                    ; Lvar r3_14076.(gv)
                    ; Lvar r4_14077.(gv)
                    ; Lvar r5_14078.(gv)
                    ; Lvar r6_14079.(gv)
                    ; Lvar r7_14080.(gv) ] __invntt___butterfly64x [:: Pvar r0_14073
                                                                    ; Pvar r1_14074
                                                                    ; Pvar r2_14075
                                                                    ; Pvar r3_14076
                                                                    ; Pvar r4_14077
                                                                    ; Pvar r5_14078
                                                                    ; Pvar r6_14079
                                                                    ; Pvar r7_14080
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_14067 ]
          ; ccall [:: Lvar r0_14073.(gv) ] __red16x [:: Pvar r0_14073
                                                      ; Pvar qx16_14067
                                                      ; Pvar vx16_14081 ]
          ; ccall [:: Lvar r0_14073.(gv); Lvar r1_14074.(gv) ] __shuffle8 [:: Pvar r0_14073
                                                                    ; Pvar r1_14074 ]
          ; ccall [:: Lvar r2_14075.(gv); Lvar r3_14076.(gv) ] __shuffle8 [:: Pvar r2_14075
                                                                    ; Pvar r3_14076 ]
          ; ccall [:: Lvar r4_14077.(gv); Lvar r5_14078.(gv) ] __shuffle8 [:: Pvar r4_14077
                                                                    ; Pvar r5_14078 ]
          ; ccall [:: Lvar r6_14079.(gv); Lvar r7_14080.(gv) ] __shuffle8 [:: Pvar r6_14079
                                                                    ; Pvar r7_14080 ]
          ; copn [:: Lvar zeta0.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (384)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))) ]
          ; copn [:: Lvar zeta1.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_inv_exp (Papp2 (Oadd (Op_int)) (Pconst (388)%Z) (Papp2 (Omul (Op_int)) (Pconst (392)%Z) (Pvar i_14068))) ]
          ; ccall [:: Lvar r0_14073.(gv)
                    ; Lvar r2_14075.(gv)
                    ; Lvar r4_14077.(gv)
                    ; Lvar r6_14079.(gv)
                    ; Lvar r1_14074.(gv)
                    ; Lvar r3_14076.(gv)
                    ; Lvar r5_14078.(gv)
                    ; Lvar r7_14080.(gv) ] __invntt___butterfly64x [:: Pvar r0_14073
                                                                    ; Pvar r2_14075
                                                                    ; Pvar r4_14077
                                                                    ; Pvar r6_14079
                                                                    ; Pvar r1_14074
                                                                    ; Pvar r3_14076
                                                                    ; Pvar r5_14078
                                                                    ; Pvar r7_14080
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_14067 ]
          ; ccall [:: Lvar r0_14073.(gv) ] __red16x [:: Pvar r0_14073
                                                      ; Pvar qx16_14067
                                                      ; Pvar vx16_14081 ]
          ; cif
              (Papp2 (Oeq (Op_int)) (Pvar i_14068) (Pconst (0)%Z))
              [:: cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068)))) (aword U256) (Pvar r0_14073)
                ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068)))) (aword U256) (Pvar r2_14075)
                ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068)))) (aword U256) (Pvar r4_14077)
                ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068)))) (aword U256) (Pvar r6_14079) ]
              [::]
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068)))) (aword U256) (Pvar r1_14074)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068)))) (aword U256) (Pvar r3_14076)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068)))) (aword U256) (Pvar r5_14078)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Pvar i_14068)))) (aword U256) (Pvar r7_14080) ]
    ; copn [:: Lvar zeta0.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_inv_exp (Pconst (784)%Z) ]
    ; copn [:: Lvar zeta1.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pget Unaligned AAdirect U32 jzetas_inv_exp (Pconst (788)%Z) ]
    ; cfor
        (i_14068.(gv))
        (UpTo, Pconst (0)%Z, Pconst (2)%Z)
        [:: cif
              (Papp2 (Oeq (Op_int)) (Pvar i_14068) (Pconst (0)%Z))
              [:: cassgn (Lvar r7_14080.(gv)) (aword U256) (Pvar r6_14079)
                ; cassgn (Lvar r6_14079.(gv)) (aword U256) (Pvar r4_14077)
                ; cassgn (Lvar r5_14078.(gv)) (aword U256) (Pvar r2_14075)
                ; cassgn (Lvar r4_14077.(gv)) (aword U256) (Pvar r0_14073) ]
              [:: cassgn (Lvar r4_14077.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068))))
                ; cassgn (Lvar r5_14078.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068))))
                ; cassgn (Lvar r6_14079.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068))))
                ; cassgn (Lvar r7_14080.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068)))) ]
          ; cassgn (Lvar r0_14073.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068))))
          ; cassgn (Lvar r1_14074.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068))))
          ; cassgn (Lvar r2_14075.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068))))
          ; cassgn (Lvar r3_14076.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14066 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068))))
          ; ccall [:: Lvar r0_14073.(gv)
                    ; Lvar r1_14074.(gv)
                    ; Lvar r2_14075.(gv)
                    ; Lvar r3_14076.(gv)
                    ; Lvar r4_14077.(gv)
                    ; Lvar r5_14078.(gv)
                    ; Lvar r6_14079.(gv)
                    ; Lvar r7_14080.(gv) ] __invntt___butterfly64x [:: Pvar r0_14073
                                                                    ; Pvar r1_14074
                                                                    ; Pvar r2_14075
                                                                    ; Pvar r3_14076
                                                                    ; Pvar r4_14077
                                                                    ; Pvar r5_14078
                                                                    ; Pvar r6_14079
                                                                    ; Pvar r7_14080
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta0
                                                                    ; Pvar zeta1
                                                                    ; Pvar zeta1
                                                                    ; Pvar qx16_14067 ]
          ; cassgn (Lvar flox16.(gv)) (aword U256) (Pget Aligned AAscale U256 jflox16 (Pconst (0)%Z))
          ; cassgn (Lvar fhix16.(gv)) (aword U256) (Pget Aligned AAscale U256 jfhix16 (Pconst (0)%Z))
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068)))) (aword U256) (Pvar r4_14077)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068)))) (aword U256) (Pvar r5_14078)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068)))) (aword U256) (Pvar r6_14079)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068)))) (aword U256) (Pvar r7_14080)
          ; ccall [:: Lvar r0_14073.(gv) ] __fqmulprecomp16x [:: Pvar r0_14073
                                                               ; Pvar flox16
                                                               ; Pvar fhix16
                                                               ; Pvar qx16_14067 ]
          ; ccall [:: Lvar r1_14074.(gv) ] __fqmulprecomp16x [:: Pvar r1_14074
                                                               ; Pvar flox16
                                                               ; Pvar fhix16
                                                               ; Pvar qx16_14067 ]
          ; ccall [:: Lvar r2_14075.(gv) ] __fqmulprecomp16x [:: Pvar r2_14075
                                                               ; Pvar flox16
                                                               ; Pvar fhix16
                                                               ; Pvar qx16_14067 ]
          ; ccall [:: Lvar r3_14076.(gv) ] __fqmulprecomp16x [:: Pvar r3_14076
                                                               ; Pvar flox16
                                                               ; Pvar fhix16
                                                               ; Pvar qx16_14067 ]
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068)))) (aword U256) (Pvar r0_14073)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068)))) (aword U256) (Pvar r1_14074)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068)))) (aword U256) (Pvar r2_14075)
          ; cassgn (Laset Unaligned AAdirect U256 rp_14066.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)) (Papp2 (Omul (Op_int)) (Pconst (128)%Z) (Pvar i_14068)))) (aword U256) (Pvar r3_14076) ] ].

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
