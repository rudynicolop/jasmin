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

(* __i_polyvec_compress *)
(* Local variables *)
Definition rp_13889 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 960) (mkident 13889).
Definition a_13890 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13890).
Definition x16p_13891 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 16) (mkident 13891).
Definition v_13892 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13892).
Definition v8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13893).
Definition off_13894 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13894).
Definition shift1_13895 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13895).
Definition mask_13896 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13896).
Definition shift2_13897 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13897).
Definition sllvdidx_13898 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13898).
Definition shufbidx_13899 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13899).
Definition i_13900 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13900).
Definition f0_13901 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13901).
Definition f1_13902 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13902).
Definition f2_13903 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13903).
Definition t0_13904 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 13904).
Definition t1_13905 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 13905).

(* Signature *)
Definition tyin___i_polyvec_compress : seq atype :=
  [:: aarr U8 960; aarr U16 768 ].
Definition args___i_polyvec_compress : seq var_i :=
  [:: rp_13889.(gv); a_13890.(gv) ].
Definition tyout___i_polyvec_compress : seq atype := [:: aarr U8 960 ].
Definition res___i_polyvec_compress : seq var_i := [:: rp_13889.(gv) ].

(* Body *)
Definition body___i_polyvec_compress : cmd :=
  [:: ccall [:: Lvar a_13890.(gv) ] __polyvec_csubq [:: Pvar a_13890 ]
    ; cassgn (Lvar x16p_13891.(gv)) (aarr U16 16) (Pvar jvx16)
    ; cassgn (Lvar v_13892.(gv)) (aword U256) (Pget Aligned AAscale U256 x16p_13891 (Pconst (0)%Z))
    ; copn [:: Lvar v8.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar v_13892
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (3)%Z) ]
    ; copn [:: Lvar off_13894.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE16 U256))))) [:: Pvar pvc_off_s ]
    ; copn [:: Lvar shift1_13895.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE16 U256))))) [:: Pvar pvc_shift1_s ]
    ; copn [:: Lvar mask_13896.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE16 U256))))) [:: Pvar pvc_mask_s ]
    ; copn [:: Lvar shift2_13897.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar pvc_shift2_s ]
    ; copn [:: Lvar sllvdidx_13898.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar pvc_sllvdidx_s ]
    ; cassgn (Lvar shufbidx_13899.(gv)) (aword U256) (Pget Aligned AAscale U256 pvc_shufbidx_s (Pconst (0)%Z))
    ; cfor
        (i_13900.(gv))
        (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (256)%Z)) (Pconst (16)%Z))
        [:: cassgn (Lvar f0_13901.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13890 (Pvar i_13900))
          ; copn [:: Lvar f1_13902.(gv) ] (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar f0_13901
                                                                    ; Pvar v8 ]
          ; copn [:: Lvar f2_13903.(gv) ] (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar f0_13901
                                                                    ; Pvar off_13894 ]
          ; copn [:: Lvar f0_13901.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar f0_13901
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (3)%Z) ]
          ; copn [:: Lvar f0_13901.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar f0_13901
                                                                    ; Pvar v_13892 ]
          ; copn [:: Lvar f2_13903.(gv) ] (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar f1_13902
                                                                    ; Pvar f2_13903 ]
          ; copn [:: Lvar f1_13902.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pvar f1_13902
                                                                    ; Pvar f2_13903 ]
          ; copn [:: Lvar f1_13902.(gv) ] (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar f1_13902
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (15)%Z) ]
          ; copn [:: Lvar f0_13901.(gv) ] (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar f0_13901
                                                                    ; Pvar f1_13902 ]
          ; copn [:: Lvar f0_13901.(gv) ] (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f0_13901
                                                                    ; Pvar shift1_13895 ]
          ; copn [:: Lvar f0_13901.(gv) ] (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f0_13901
                                                                    ; Pvar mask_13896 ]
          ; copn [:: Lvar f0_13901.(gv) ] (Oasm ((BaseOp ((None), (VPMADDWD U256))))) [:: Pvar f0_13901
                                                                    ; Pvar shift2_13897 ]
          ; copn [:: Lvar f0_13901.(gv) ] (Oasm ((BaseOp ((None), (VPSLLV VE32 U256))))) [:: Pvar f0_13901
                                                                    ; Pvar sllvdidx_13898 ]
          ; copn [:: Lvar f0_13901.(gv) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pvar f0_13901
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (12)%Z) ]
          ; copn [:: Lvar f0_13901.(gv) ] (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f0_13901
                                                                    ; Pvar shufbidx_13899 ]
          ; cassgn (Lvar t0_13904.(gv)) (aword U128) (Pvar f0_13901)
          ; copn [:: Lvar t1_13905.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar f0_13901
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; copn [:: Lvar t0_13904.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE16 U128))))) [:: Pvar t0_13904
                                                                    ; Pvar t1_13905
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (224)%Z) ]
          ; cassgn (Laset Unaligned AAdirect U128 rp_13889.(gv) (Papp2 (Omul (Op_int)) (Pconst (20)%Z) (Pvar i_13900))) (aword U128) (Pvar t0_13904)
          ; copn [:: Laset Unaligned AAdirect U32 rp_13889.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (20)%Z) (Pvar i_13900)) (Pconst (16)%Z)) ] (Oasm ((BaseOp ((None), (VPEXTR U32))))) [:: Pvar t1_13905
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (0)%Z) ] ] ].

Definition fd___i_polyvec_compress : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___i_polyvec_compress;
    f_params := args___i_polyvec_compress;
    f_body := body___i_polyvec_compress;
    f_tyout := tyout___i_polyvec_compress;
    f_res := res___i_polyvec_compress;
    f_extra := tt;
  |}.

End IDO.
