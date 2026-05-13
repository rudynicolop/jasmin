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

(* _i_poly_tobytes *)
(* Local variables *)
Definition rp_13996 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 384) (mkident 13996).
Definition a_13997 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13997).
Definition i_13998 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13998).
Definition t0_13999 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13999).
Definition t1_14000 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14000).
Definition t2_14001 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14001).
Definition t3_14002 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14002).
Definition t4_14003 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14003).
Definition t5_14004 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14004).
Definition t6_14005 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14005).
Definition t7_14006 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14006).
Definition j_tt_14007 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14007).
Definition ttt : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14008).

(* Signature *)
Definition tyin__i_poly_tobytes : seq atype :=
  [:: aarr U8 384; aarr U16 256 ].
Definition args__i_poly_tobytes : seq var_i :=
  [:: rp_13996.(gv); a_13997.(gv) ].
Definition tyout__i_poly_tobytes : seq atype :=
  [:: aarr U8 384; aarr U16 256 ].
Definition res__i_poly_tobytes : seq var_i :=
  [:: rp_13996.(gv); a_13997.(gv) ].

(* Body *)
Definition body__i_poly_tobytes : cmd :=
  [:: ccall [:: Lvar a_13997.(gv) ] _poly_csubq [:: Pvar a_13997 ]
    ; cfor
        (i_13998.(gv))
        (UpTo, Pconst (0)%Z, Pconst (2)%Z)
        [:: cassgn (Lvar t0_13999.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13997 (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_13998)))
          ; cassgn (Lvar t1_14000.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13997 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_13998)) (Pconst (1)%Z)))
          ; cassgn (Lvar t2_14001.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13997 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_13998)) (Pconst (2)%Z)))
          ; cassgn (Lvar t3_14002.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13997 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_13998)) (Pconst (3)%Z)))
          ; cassgn (Lvar t4_14003.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13997 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_13998)) (Pconst (4)%Z)))
          ; cassgn (Lvar t5_14004.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13997 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_13998)) (Pconst (5)%Z)))
          ; cassgn (Lvar t6_14005.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13997 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_13998)) (Pconst (6)%Z)))
          ; cassgn (Lvar t7_14006.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13997 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_13998)) (Pconst (7)%Z)))
          ; copn [:: Lvar j_tt_14007.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t1_14000
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (12)%Z) ]
          ; cassgn (Lvar j_tt_14007.(gv)) (aword U256) (Papp2 (Olor U256) (Pvar j_tt_14007) (Pvar t0_13999))
          ; copn [:: Lvar t0_13999.(gv) ] (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t1_14000
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ]
          ; copn [:: Lvar t1_14000.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t2_14001
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ]
          ; cassgn (Lvar t0_13999.(gv)) (aword U256) (Papp2 (Olor U256) (Pvar t0_13999) (Pvar t1_14000))
          ; copn [:: Lvar t1_14000.(gv) ] (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t2_14001
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ]
          ; copn [:: Lvar t2_14001.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t3_14002
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ]
          ; cassgn (Lvar t1_14000.(gv)) (aword U256) (Papp2 (Olor U256) (Pvar t1_14000) (Pvar t2_14001))
          ; copn [:: Lvar t2_14001.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t5_14004
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (12)%Z) ]
          ; cassgn (Lvar t2_14001.(gv)) (aword U256) (Papp2 (Olor U256) (Pvar t2_14001) (Pvar t4_14003))
          ; copn [:: Lvar t3_14002.(gv) ] (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t5_14004
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ]
          ; copn [:: Lvar t4_14003.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t6_14005
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ]
          ; cassgn (Lvar t3_14002.(gv)) (aword U256) (Papp2 (Olor U256) (Pvar t3_14002) (Pvar t4_14003))
          ; copn [:: Lvar t4_14003.(gv) ] (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar t6_14005
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ]
          ; copn [:: Lvar t5_14004.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar t7_14006
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ]
          ; cassgn (Lvar t4_14003.(gv)) (aword U256) (Papp2 (Olor U256) (Pvar t4_14003) (Pvar t5_14004))
          ; ccall [:: Lvar ttt.(gv); Lvar t0_13999.(gv) ] __shuffle1 [:: Pvar j_tt_14007
                                                                    ; Pvar t0_13999 ]
          ; ccall [:: Lvar j_tt_14007.(gv); Lvar t2_14001.(gv) ] __shuffle1 [:: Pvar t1_14000
                                                                    ; Pvar t2_14001 ]
          ; ccall [:: Lvar t1_14000.(gv); Lvar t4_14003.(gv) ] __shuffle1 [:: Pvar t3_14002
                                                                    ; Pvar t4_14003 ]
          ; ccall [:: Lvar t3_14002.(gv); Lvar j_tt_14007.(gv) ] __shuffle2 [:: Pvar ttt
                                                                    ; Pvar j_tt_14007 ]
          ; ccall [:: Lvar ttt.(gv); Lvar t0_13999.(gv) ] __shuffle2 [:: Pvar t1_14000
                                                                    ; Pvar t0_13999 ]
          ; ccall [:: Lvar t1_14000.(gv); Lvar t4_14003.(gv) ] __shuffle2 [:: Pvar t2_14001
                                                                    ; Pvar t4_14003 ]
          ; ccall [:: Lvar t2_14001.(gv); Lvar ttt.(gv) ] __shuffle4 [:: Pvar t3_14002
                                                                    ; Pvar ttt ]
          ; ccall [:: Lvar t3_14002.(gv); Lvar j_tt_14007.(gv) ] __shuffle4 [:: Pvar t1_14000
                                                                    ; Pvar j_tt_14007 ]
          ; ccall [:: Lvar t1_14000.(gv); Lvar t4_14003.(gv) ] __shuffle4 [:: Pvar t0_13999
                                                                    ; Pvar t4_14003 ]
          ; ccall [:: Lvar t0_13999.(gv); Lvar t3_14002.(gv) ] __shuffle8 [:: Pvar t2_14001
                                                                    ; Pvar t3_14002 ]
          ; ccall [:: Lvar t2_14001.(gv); Lvar ttt.(gv) ] __shuffle8 [:: Pvar t1_14000
                                                                    ; Pvar ttt ]
          ; ccall [:: Lvar t1_14000.(gv); Lvar t4_14003.(gv) ] __shuffle8 [:: Pvar j_tt_14007
                                                                    ; Pvar t4_14003 ]
          ; cassgn (Laset Unaligned AAdirect U256 rp_13996.(gv) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_13998))) (aword U256) (Pvar t0_13999)
          ; cassgn (Laset Unaligned AAdirect U256 rp_13996.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_13998)) (Pconst (32)%Z))) (aword U256) (Pvar t2_14001)
          ; cassgn (Laset Unaligned AAdirect U256 rp_13996.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_13998)) (Pconst (64)%Z))) (aword U256) (Pvar t1_14000)
          ; cassgn (Laset Unaligned AAdirect U256 rp_13996.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_13998)) (Pconst (96)%Z))) (aword U256) (Pvar t3_14002)
          ; cassgn (Laset Unaligned AAdirect U256 rp_13996.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_13998)) (Pconst (128)%Z))) (aword U256) (Pvar ttt)
          ; cassgn (Laset Unaligned AAdirect U256 rp_13996.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (192)%Z) (Pvar i_13998)) (Pconst (160)%Z))) (aword U256) (Pvar t4_14003) ] ].

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
