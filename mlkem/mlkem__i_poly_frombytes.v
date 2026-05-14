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
Definition rp_14183 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14183).
Definition ap_14184 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 384) (mkident 14184).
Definition mask : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14185).
Definition i_14186 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14186).
Definition t0_14187 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14187).
Definition t1_14188 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14188).
Definition t2_14189 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14189).
Definition t3_14190 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14190).
Definition t4_14191 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14191).
Definition t5_14192 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14192).
Definition j_tt : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14193).
Definition t6_14194 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14194).
Definition t7_14195 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14195).
Definition t8_14196 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14196).
Definition t9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14197).
Definition t10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14198).
Definition t11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14199).

(* Signature *)
Definition tyin__i_poly_frombytes : seq atype :=
  [:: aarr U16 256; aarr U8 384 ].
Definition args__i_poly_frombytes : seq var_i :=
  [:: rp_14183.(gv); ap_14184.(gv) ].
Definition tyout__i_poly_frombytes : seq atype := [:: aarr U16 256 ].
Definition res__i_poly_frombytes : seq var_i := [:: rp_14183.(gv) ].

(* Body *)
Definition body__i_poly_frombytes : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar mask.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 maskx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cfor
                              (i_14186.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (2)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_14187.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_14184 (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_14186))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_14188.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_14184 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_14186)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_14189.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_14184 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_14186)) (Pconst (64)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_14190.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_14184 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_14186)) (Pconst (96)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t4_14191.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_14184 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_14186)) (Pconst (128)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t5_14192.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_14184 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_14186)) (Pconst (160)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar j_tt.(gv)
                                                                ; Lvar t3_14190.(gv) ] __shuffle8 [:: Pvar t0_14187
                                                                    ; Pvar t3_14190 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t0_14187.(gv)
                                                                ; Lvar t4_14191.(gv) ] __shuffle8 [:: Pvar t1_14188
                                                                    ; Pvar t4_14191 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t1_14188.(gv)
                                                                ; Lvar t5_14192.(gv) ] __shuffle8 [:: Pvar t2_14189
                                                                    ; Pvar t5_14192 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t2_14189.(gv)
                                                                ; Lvar t4_14191.(gv) ] __shuffle4 [:: Pvar j_tt
                                                                    ; Pvar t4_14191 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar j_tt.(gv)
                                                                ; Lvar t1_14188.(gv) ] __shuffle4 [:: Pvar t3_14190
                                                                    ; Pvar t1_14188 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t3_14190.(gv)
                                                                ; Lvar t5_14192.(gv) ] __shuffle4 [:: Pvar t0_14187
                                                                    ; Pvar t5_14192 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t0_14187.(gv)
                                                                ; Lvar t1_14188.(gv) ] __shuffle2 [:: Pvar t2_14189
                                                                    ; Pvar t1_14188 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t2_14189.(gv)
                                                                ; Lvar t3_14190.(gv) ] __shuffle2 [:: Pvar t4_14191
                                                                    ; Pvar t3_14190 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t4_14191.(gv)
                                                                ; Lvar t5_14192.(gv) ] __shuffle2 [:: Pvar j_tt
                                                                    ; Pvar t5_14192 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t6_14194.(gv)
                                                                ; Lvar t3_14190.(gv) ] __shuffle1 [:: Pvar t0_14187
                                                                    ; Pvar t3_14190 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t0_14187.(gv)
                                                                ; Lvar t4_14191.(gv) ] __shuffle1 [:: Pvar t1_14188
                                                                    ; Pvar t4_14191 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t1_14188.(gv)
                                                                ; Lvar t5_14192.(gv) ] __shuffle1 [:: Pvar t2_14189
                                                                    ; Pvar t5_14192 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t7_14195.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t6_14194
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (12)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t8_14196.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t3_14190
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t7_14195.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPOR U256))))) [:: Pvar t7_14195
                                                                    ; Pvar t8_14196 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t6_14194.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t6_14194 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t7_14195.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t7_14195 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t8_14196.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t3_14190
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t0_14187
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t8_14196.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPOR U256))))) [:: Pvar t8_14196
                                                                    ; Pvar t9 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t8_14196.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t8_14196 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t0_14187
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t9.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t9 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t4_14191
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (12)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t1_14188
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPOR U256))))) [:: Pvar t10
                                                                    ; Pvar t11 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t4_14191.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t4_14191 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t10 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t1_14188
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar j_tt.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t5_14192
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPOR U256))))) [:: Pvar t11
                                                                    ; Pvar j_tt ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t11.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar t11 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar j_tt.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t5_14192
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar j_tt.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask
                                                                    ; Pvar j_tt ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_14183.(gv) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_14186))) AT_none (aword U256) (Pvar t6_14194))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_14183.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_14186)) (Pconst (1)%Z))) AT_none (aword U256) (Pvar t7_14195))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_14183.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_14186)) (Pconst (2)%Z))) AT_none (aword U256) (Pvar t8_14196))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_14183.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_14186)) (Pconst (3)%Z))) AT_none (aword U256) (Pvar t9))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_14183.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_14186)) (Pconst (4)%Z))) AT_none (aword U256) (Pvar t4_14191))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_14183.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_14186)) (Pconst (5)%Z))) AT_none (aword U256) (Pvar t10))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_14183.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_14186)) (Pconst (6)%Z))) AT_none (aword U256) (Pvar t11))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_14183.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_14186)) (Pconst (7)%Z))) AT_none (aword U256) (Pvar j_tt)) ]) ].

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
