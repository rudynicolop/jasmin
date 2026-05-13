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

(* _i_poly_compress *)
(* Local variables *)
Definition rp_13964 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 13964).
Definition a_13965 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13965).
Definition x16p : gvar := mk_rocq_gvar Slocal (aarr U16 16) (mkident 13966).
Definition v : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13967).
Definition shift1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13968).
Definition mask_13969 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13969).
Definition shift2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13970).
Definition permidx : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13971).
Definition i_13972 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13972).
Definition f0_13973 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13973).
Definition f1_13974 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13974).
Definition f2_13975 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13975).
Definition f3_13976 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13976).

(* Signature *)
Definition tyin__i_poly_compress : seq atype :=
  [:: aarr U8 128; aarr U16 256 ].
Definition args__i_poly_compress : seq var_i :=
  [:: rp_13964.(gv); a_13965.(gv) ].
Definition tyout__i_poly_compress : seq atype :=
  [:: aarr U8 128; aarr U16 256 ].
Definition res__i_poly_compress : seq var_i :=
  [:: rp_13964.(gv); a_13965.(gv) ].

(* Body *)
Definition body__i_poly_compress : cmd :=
  [:: ccall [:: Lvar a_13965.(gv) ] _poly_csubq [:: Pvar a_13965 ]
    ; cassgn (Lvar x16p.(gv)) (aarr U16 16) (Pvar jvx16)
    ; cassgn (Lvar v.(gv)) (aword U256) (Pget Aligned AAscale U256 x16p (Pconst (0)%Z))
    ; copn [:: Lvar shift1.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE16 U256))))) [:: Pvar pc_shift1_s ]
    ; copn [:: Lvar mask_13969.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE16 U256))))) [:: Pvar pc_mask_s ]
    ; copn [:: Lvar shift2.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE16 U256))))) [:: Pvar pc_shift2_s ]
    ; cassgn (Lvar permidx.(gv)) (aword U256) (Pget Aligned AAscale U256 pc_permidx_s (Pconst (0)%Z))
    ; cfor
        (i_13972.(gv))
        (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (256)%Z) (Pconst (64)%Z))
        [:: cassgn (Lvar f0_13973.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13965 (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_13972)))
          ; cassgn (Lvar f1_13974.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13965 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_13972)) (Pconst (1)%Z)))
          ; cassgn (Lvar f2_13975.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13965 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_13972)) (Pconst (2)%Z)))
          ; cassgn (Lvar f3_13976.(gv)) (aword U256) (Pget Aligned AAscale U256 a_13965 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_13972)) (Pconst (3)%Z)))
          ; copn [:: Lvar f0_13973.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar f0_13973
                                                                    ; Pvar v ]
          ; copn [:: Lvar f1_13974.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar f1_13974
                                                                    ; Pvar v ]
          ; copn [:: Lvar f2_13975.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar f2_13975
                                                                    ; Pvar v ]
          ; copn [:: Lvar f3_13976.(gv) ] (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar f3_13976
                                                                    ; Pvar v ]
          ; copn [:: Lvar f0_13973.(gv) ] (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f0_13973
                                                                    ; Pvar shift1 ]
          ; copn [:: Lvar f1_13974.(gv) ] (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f1_13974
                                                                    ; Pvar shift1 ]
          ; copn [:: Lvar f2_13975.(gv) ] (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f2_13975
                                                                    ; Pvar shift1 ]
          ; copn [:: Lvar f3_13976.(gv) ] (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f3_13976
                                                                    ; Pvar shift1 ]
          ; copn [:: Lvar f0_13973.(gv) ] (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f0_13973
                                                                    ; Pvar mask_13969 ]
          ; copn [:: Lvar f1_13974.(gv) ] (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f1_13974
                                                                    ; Pvar mask_13969 ]
          ; copn [:: Lvar f2_13975.(gv) ] (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f2_13975
                                                                    ; Pvar mask_13969 ]
          ; copn [:: Lvar f3_13976.(gv) ] (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f3_13976
                                                                    ; Pvar mask_13969 ]
          ; copn [:: Lvar f0_13973.(gv) ] (Oasm ((BaseOp ((None), (VPACKUS VE16 U256))))) [:: Pvar f0_13973
                                                                    ; Pvar f1_13974 ]
          ; copn [:: Lvar f2_13975.(gv) ] (Oasm ((BaseOp ((None), (VPACKUS VE16 U256))))) [:: Pvar f2_13975
                                                                    ; Pvar f3_13976 ]
          ; copn [:: Lvar f0_13973.(gv) ] (Oasm ((BaseOp ((None), (VPMADDUBSW U256))))) [:: Pvar f0_13973
                                                                    ; Pvar shift2 ]
          ; copn [:: Lvar f2_13975.(gv) ] (Oasm ((BaseOp ((None), (VPMADDUBSW U256))))) [:: Pvar f2_13975
                                                                    ; Pvar shift2 ]
          ; copn [:: Lvar f0_13973.(gv) ] (Oasm ((BaseOp ((None), (VPACKUS VE16 U256))))) [:: Pvar f0_13973
                                                                    ; Pvar f2_13975 ]
          ; copn [:: Lvar f0_13973.(gv) ] (Oasm ((BaseOp ((None), VPERMD)))) [:: Pvar permidx
                                                                    ; Pvar f0_13973 ]
          ; cassgn (Laset Unaligned AAdirect U256 rp_13964.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_13972))) (aword U256) (Pvar f0_13973) ] ].

Definition fd__i_poly_compress : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__i_poly_compress;
    f_params := args__i_poly_compress;
    f_body := body__i_poly_compress;
    f_tyout := tyout__i_poly_compress;
    f_res := res__i_poly_compress;
    f_extra := tt;
  |}.

End IDO.
