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

(* __i_polyvec_decompress *)
(* Local variables *)
Definition rp_13909 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13909).
Definition r_13910 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 768) (mkident 13910).
Definition q_13911 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13911).
Definition shufbidx_13912 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13912).
Definition sllvdidx : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13913).
Definition mask_13914 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13914).
Definition i_13915 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13915).
Definition k : gvar := mk_rocq_gvar Slocal (aint) (mkident 13916).
Definition f_13917 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13917).

(* Signature *)
Definition tyin___i_polyvec_decompress : seq atype := [:: aarr U8 1088 ].
Definition args___i_polyvec_decompress : seq var_i := [:: rp_13909.(gv) ].
Definition tyout___i_polyvec_decompress : seq atype := [:: aarr U16 768 ].
Definition res___i_polyvec_decompress : seq var_i := [:: r_13910.(gv) ].

(* Body *)
Definition body___i_polyvec_decompress : cmd :=
  [:: copn [:: Lvar q_13911.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pvar pvd_q_s ]
    ; cassgn (Lvar shufbidx_13912.(gv)) (aword U256) (Pget Aligned AAscale U256 pvd_shufbdidx_s (Pconst (0)%Z))
    ; copn [:: Lvar sllvdidx.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar pvd_sllvdidx_s ]
    ; copn [:: Lvar mask_13914.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pvar pvd_mask_s ]
    ; cfor
        (k.(gv))
        (UpTo, Pconst (0)%Z, Pconst (3)%Z)
        [:: cfor
              (i_13915.(gv))
              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (256)%Z) (Pconst (16)%Z))
              [:: cassgn (Lvar f_13917.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_13909 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (320)%Z) (Pvar k)) (Papp2 (Omul (Op_int)) (Pconst (20)%Z) (Pvar i_13915))))
                ; copn [:: Lvar f_13917.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar f_13917
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (148)%Z) ]
                ; copn [:: Lvar f_13917.(gv) ] (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f_13917
                                                                    ; Pvar shufbidx_13912 ]
                ; copn [:: Lvar f_13917.(gv) ] (Oasm ((BaseOp ((None), (VPSLLV VE32 U256))))) [:: Pvar f_13917
                                                                    ; Pvar sllvdidx ]
                ; copn [:: Lvar f_13917.(gv) ] (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar f_13917
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ]
                ; copn [:: Lvar f_13917.(gv) ] (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f_13917
                                                                    ; Pvar mask_13914 ]
                ; copn [:: Lvar f_13917.(gv) ] (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f_13917
                                                                    ; Pvar q_13911 ]
                ; cassgn (Laset Aligned AAscale U256 r_13910.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (16)%Z) (Pvar k)) (Pvar i_13915))) (aword U256) (Pvar f_13917) ] ] ].

Definition fd___i_polyvec_decompress : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___i_polyvec_decompress;
    f_params := args___i_polyvec_decompress;
    f_body := body___i_polyvec_decompress;
    f_tyout := tyout___i_polyvec_decompress;
    f_res := res___i_polyvec_decompress;
    f_extra := tt;
  |}.

End IDO.
