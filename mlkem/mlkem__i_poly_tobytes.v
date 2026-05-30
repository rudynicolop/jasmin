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

(* _i_poly_tobytes *)
(* Local variables *)
Definition rp_13 : gvar := mk_rocq_gvar Slocal (aarr U8 384) (mkident 13996).
Definition a_33 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13997).
Definition i_83 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13998).
Definition t0_29 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13999).
Definition t1_29 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14000).
Definition t2_27 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14001).
Definition t3_27 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14002).
Definition t4_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14003).
Definition t5_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14004).
Definition t6_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14005).
Definition t7_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14006).
Definition j_tt_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14007).
Definition ttt : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14008).

(* Signature *)
Definition tyin__i_poly_tobytes : seq atype :=
  [:: aarr U8 384; aarr U16 256 ].
Definition args__i_poly_tobytes : seq var_i := [:: rp_13.(gv); a_33.(gv) ].
Definition tyout__i_poly_tobytes : seq atype :=
  [:: aarr U8 384; aarr U16 256 ].
Definition res__i_poly_tobytes : seq var_i := [:: rp_13.(gv); a_33.(gv) ].

(* Body *)
Definition body__i_poly_tobytes : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar a_33.(gv) ] _poly_csubq [:: Pvar a_33 ])
    ; MkI dummy_instr_info (Cfor
                              (i_83.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (2)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_29.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_33 (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_83))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_29.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_33 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_83)) (Pconst (1)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_27.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_33 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_83)) (Pconst (2)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_27.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_33 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_83)) (Pconst (3)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t4_2.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_33 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_83)) (Pconst (4)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t5_2.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_33 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_83)) (Pconst (5)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t6_2.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_33 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_83)) (Pconst (6)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar t7_2.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_33 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_83)) (Pconst (7)%Z))))
                                ; MkI dummy_instr_info (Copn [:: Lvar j_tt_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t1_29
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (12)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar j_tt_0.(gv)) AT_none (aword U256) (Papp2 (Olor U256) (Pvar j_tt_0) (Pvar t0_29)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t0_29.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t1_29
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t1_29.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t2_27
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t0_29.(gv)) AT_none (aword U256) (Papp2 (Olor U256) (Pvar t0_29) (Pvar t1_29)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t1_29.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t2_27
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t2_27.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t3_27
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_29.(gv)) AT_none (aword U256) (Papp2 (Olor U256) (Pvar t1_29) (Pvar t2_27)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t2_27.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t5_2
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (12)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_27.(gv)) AT_none (aword U256) (Papp2 (Olor U256) (Pvar t2_27) (Pvar t4_2)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t3_27.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t5_2
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t4_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t6_2
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_27.(gv)) AT_none (aword U256) (Papp2 (Olor U256) (Pvar t3_27) (Pvar t4_2)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t4_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t6_2
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t5_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t7_2
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t4_2.(gv)) AT_none (aword U256) (Papp2 (Olor U256) (Pvar t4_2) (Pvar t5_2)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar ttt.(gv)
                                                                ; Lvar t0_29.(gv) ] __shuffle1 [:: Pvar j_tt_0
                                                                    ; Pvar t0_29 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar j_tt_0.(gv)
                                                                ; Lvar t2_27.(gv) ] __shuffle1 [:: Pvar t1_29
                                                                    ; Pvar t2_27 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t1_29.(gv)
                                                                ; Lvar t4_2.(gv) ] __shuffle1 [:: Pvar t3_27
                                                                    ; Pvar t4_2 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t3_27.(gv)
                                                                ; Lvar j_tt_0.(gv) ] __shuffle2 [:: Pvar ttt
                                                                    ; Pvar j_tt_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar ttt.(gv)
                                                                ; Lvar t0_29.(gv) ] __shuffle2 [:: Pvar t1_29
                                                                    ; Pvar t0_29 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t1_29.(gv)
                                                                ; Lvar t4_2.(gv) ] __shuffle2 [:: Pvar t2_27
                                                                    ; Pvar t4_2 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t2_27.(gv)
                                                                ; Lvar ttt.(gv) ] __shuffle4 [:: Pvar t3_27
                                                                    ; Pvar ttt ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t3_27.(gv)
                                                                ; Lvar j_tt_0.(gv) ] __shuffle4 [:: Pvar t1_29
                                                                    ; Pvar j_tt_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t1_29.(gv)
                                                                ; Lvar t4_2.(gv) ] __shuffle4 [:: Pvar t0_29
                                                                    ; Pvar t4_2 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t0_29.(gv)
                                                                ; Lvar t3_27.(gv) ] __shuffle8 [:: Pvar t2_27
                                                                    ; Pvar t3_27 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t2_27.(gv)
                                                                ; Lvar ttt.(gv) ] __shuffle8 [:: Pvar t1_29
                                                                    ; Pvar ttt ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar t1_29.(gv)
                                                                ; Lvar t4_2.(gv) ] __shuffle8 [:: Pvar j_tt_0
                                                                    ; Pvar t4_2 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_13.(gv) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_83))) AT_none (aword U256) (Pvar t0_29))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_13.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_83)) (Pconst (32)%Z))) AT_none (aword U256) (Pvar t2_27))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_13.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_83)) (Pconst (64)%Z))) AT_none (aword U256) (Pvar t1_29))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_13.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_83)) (Pconst (96)%Z))) AT_none (aword U256) (Pvar t3_27))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_13.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_83)) (Pconst (128)%Z))) AT_none (aword U256) (Pvar ttt))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_13.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_83)) (Pconst (160)%Z))) AT_none (aword U256) (Pvar t4_2)) ]) ].

Definition fd__i_poly_tobytes : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__i_poly_tobytes;
    f_params := args__i_poly_tobytes;
    f_body := body__i_poly_tobytes;
    f_tyout := tyout__i_poly_tobytes;
    f_res := res__i_poly_tobytes;
    f_extra := tt;
  |}.

End IDO.
