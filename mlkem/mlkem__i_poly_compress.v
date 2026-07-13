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

(* _i_poly_compress *)
(* Local variables *)
Definition rp_15 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 13964).
Definition a_35 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13965).
Definition x16p : gvar := mk_rocq_gvar Slocal (aarr U16 16) (mkident 13966).
Definition v : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13967).
Definition shift1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13968).
Definition mask_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13969).
Definition shift2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13970).
Definition permidx : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13971).
Definition i_85 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13972).
Definition f0_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13973).
Definition f1_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13974).
Definition f2_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13975).
Definition f3_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13976).

(* Signature *)
Definition tyin__i_poly_compress : seq atype :=
  [:: aarr U8 128; aarr U16 256 ].
Definition args__i_poly_compress : seq var_i := [:: rp_15.(gv); a_35.(gv) ].
Definition tyout__i_poly_compress : seq atype :=
  [:: aarr U8 128; aarr U16 256 ].
Definition res__i_poly_compress : seq var_i := [:: rp_15.(gv); a_35.(gv) ].

(* Body *)
Definition body__i_poly_compress : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar a_35.(gv) ] _poly_csubq [:: Pvar a_35 ])
    ; MkI dummy_instr_info (Cassgn (Lvar x16p.(gv)) AT_none (aarr U16 16) (Pvar jvx16))
    ; MkI dummy_instr_info (Cassgn (Lvar v.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 x16p (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar shift1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE16 U256))))) [:: Pvar pc_shift1_s ])
    ; MkI dummy_instr_info (Copn [:: Lvar mask_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE16 U256))))) [:: Pvar pc_mask_s ])
    ; MkI dummy_instr_info (Copn [:: Lvar shift2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE16 U256))))) [:: Pvar pc_shift2_s ])
    ; MkI dummy_instr_info (Cassgn (Lvar permidx.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 pc_permidx_s (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cfor
                              (i_85.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (256)%Z) (Pconst (64)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar f0_1.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_35 (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_85))))
                                ; MkI dummy_instr_info (Cassgn (Lvar f1_1.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_35 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_85)) (Pconst (1)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar f2_0.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_35 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_85)) (Pconst (2)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar f3_0.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_35 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_85)) (Pconst (3)%Z))))
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar f0_1
                                                                    ; Pvar v ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar f1_1
                                                                    ; Pvar v ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar f2_0
                                                                    ; Pvar v ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f3_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULH U256))))) [:: Pvar f3_0
                                                                    ; Pvar v ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f0_1
                                                                    ; Pvar shift1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f1_1
                                                                    ; Pvar shift1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f2_0
                                                                    ; Pvar shift1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f3_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f3_0
                                                                    ; Pvar shift1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f0_1
                                                                    ; Pvar mask_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f1_1
                                                                    ; Pvar mask_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f2_0
                                                                    ; Pvar mask_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f3_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f3_0
                                                                    ; Pvar mask_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPACKUS VE16 U256))))) [:: Pvar f0_1
                                                                    ; Pvar f1_1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPACKUS VE16 U256))))) [:: Pvar f2_0
                                                                    ; Pvar f3_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMADDUBSW U256))))) [:: Pvar f0_1
                                                                    ; Pvar shift2 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMADDUBSW U256))))) [:: Pvar f2_0
                                                                    ; Pvar shift2 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPACKUS VE16 U256))))) [:: Pvar f0_1
                                                                    ; Pvar f2_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMD)))) [:: Pvar permidx
                                                                    ; Pvar f0_1 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_15.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_85))) AT_none (aword U256) (Pvar f0_1)) ]) ].

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
