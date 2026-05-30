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

(* _i_poly_frombytes *)
(* Local variables *)
Definition rp_3 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14183).
Definition ap_0 : gvar := mk_rocq_gvar Slocal (aarr U8 384) (mkident 14184).
Definition mask : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14185).
Definition i_75 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14186).
Definition t0_26 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14187).
Definition t1_26 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14188).
Definition t2_24 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14189).
Definition t3_24 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14190).
Definition t4_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14191).
Definition t5_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14192).
Definition j_tt : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14193).
Definition t6_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14194).
Definition t7_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14195).
Definition t8_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14196).
Definition t9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14197).
Definition t10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14198).
Definition t11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14199).

(* Signature *)
Definition tyin__i_poly_frombytes : seq atype :=
  [:: aarr U16 256; aarr U8 384 ].
Definition args__i_poly_frombytes : seq var_i := [:: rp_3.(gv); ap_0.(gv) ].
Definition tyout__i_poly_frombytes : seq atype := [:: aarr U16 256 ].
Definition res__i_poly_frombytes : seq var_i := [:: rp_3.(gv) ].

(* Body *)
Definition body__i_poly_frombytes : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar mask.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 maskx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cfor
                              (i_75.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (2)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_26.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_0 (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_75))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_26.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_75)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_24.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_75)) (Pconst (64)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_24.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_75)) (Pconst (96)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t4_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_75)) (Pconst (128)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t5_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_75)) (Pconst (160)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar j_tt.(gv)
                                                                ; Lvar t3_24.(gv) ] __shuffle8 [:: Pvar t0_26
                                                                    ; Pvar t3_24 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t0_26.(gv)
                                                                ; Lvar t4_0.(gv) ] __shuffle8 [:: Pvar t1_26
                                                                    ; Pvar t4_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t1_26.(gv)
                                                                ; Lvar t5_0.(gv) ] __shuffle8 [:: Pvar t2_24
                                                                    ; Pvar t5_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t2_24.(gv)
                                                                ; Lvar t4_0.(gv) ] __shuffle4 [:: Pvar j_tt
                                                                    ; Pvar t4_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar j_tt.(gv)
                                                                ; Lvar t1_26.(gv) ] __shuffle4 [:: Pvar t3_24
                                                                    ; Pvar t1_26 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t3_24.(gv)
                                                                ; Lvar t5_0.(gv) ] __shuffle4 [:: Pvar t0_26
                                                                    ; Pvar t5_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t0_26.(gv)
                                                                ; Lvar t1_26.(gv) ] __shuffle2 [:: Pvar t2_24
                                                                    ; Pvar t1_26 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t2_24.(gv)
                                                                ; Lvar t3_24.(gv) ] __shuffle2 [:: Pvar t4_0
                                                                    ; Pvar t3_24 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t4_0.(gv)
                                                                ; Lvar t5_0.(gv) ] __shuffle2 [:: Pvar j_tt
                                                                    ; Pvar t5_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t6_0.(gv)
                                                                ; Lvar t3_24.(gv) ] __shuffle1 [:: Pvar t0_26
                                                                    ; Pvar t3_24 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t0_26.(gv)
                                                                ; Lvar t4_0.(gv) ] __shuffle1 [:: Pvar t1_26
                                                                    ; Pvar t4_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t1_26.(gv)
                                                                ; Lvar t5_0.(gv) ] __shuffle1 [:: Pvar t2_24
                                                                    ; Pvar t5_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t7_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t6_0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (12)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t8_12.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t3_24
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t7_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPOR U256))))) [:: Pvar t7_0
                                                                    ; Pvar t8_12 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t6_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t6_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t7_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t7_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t8_12.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t3_24
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t0_26
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t8_12.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPOR U256))))) [:: Pvar t8_12
                                                                    ; Pvar t9 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t8_12.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t8_12 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t0_26
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t9 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t4_0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (12)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t1_26
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPOR U256))))) [:: Pvar t10
                                                                    ; Pvar t11 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t4_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t4_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t10 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t1_26
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar j_tt.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t5_0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPOR U256))))) [:: Pvar t11
                                                                    ; Pvar j_tt ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t11 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar j_tt.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t5_0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar j_tt.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar j_tt ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_3.(gv) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_75))) AT_none (aword U256) (Pvar t6_0))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_3.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_75)) (Pconst (1)%Z))) AT_none (aword U256) (Pvar t7_0))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_3.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_75)) (Pconst (2)%Z))) AT_none (aword U256) (Pvar t8_12))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_3.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_75)) (Pconst (3)%Z))) AT_none (aword U256) (Pvar t9))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_3.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_75)) (Pconst (4)%Z))) AT_none (aword U256) (Pvar t4_0))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_3.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_75)) (Pconst (5)%Z))) AT_none (aword U256) (Pvar t10))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_3.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_75)) (Pconst (6)%Z))) AT_none (aword U256) (Pvar t11))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_3.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_75)) (Pconst (7)%Z))) AT_none (aword U256) (Pvar j_tt)) ]) ].

Definition fd__i_poly_frombytes : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__i_poly_frombytes;
    f_params := args__i_poly_frombytes;
    f_body := body__i_poly_frombytes;
    f_tyout := tyout__i_poly_frombytes;
    f_res := res__i_poly_frombytes;
    f_extra := tt;
  |}.

End IDO.
