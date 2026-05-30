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

(* _i_poly_tomsg *)
(* Local variables *)
Definition rp_14 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13981).
Definition a_34 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13982).
Definition px16 : gvar := mk_rocq_gvar Slocal (aarr U16 16) (mkident 13983).
Definition hq : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13984).
Definition hhq : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13985).
Definition i_84 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13986).
Definition f0_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13987).
Definition f1_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13988).
Definition g0_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13989).
Definition g1_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13990).
Definition c_0 : gvar := mk_rocq_gvar Slocal (aword U32) (mkident 13991).

(* Signature *)
Definition tyin__i_poly_tomsg : seq atype := [:: aarr U8 32; aarr U16 256 ].
Definition args__i_poly_tomsg : seq var_i := [:: rp_14.(gv); a_34.(gv) ].
Definition tyout__i_poly_tomsg : seq atype := [:: aarr U8 32; aarr U16 256 ].
Definition res__i_poly_tomsg : seq var_i := [:: rp_14.(gv); a_34.(gv) ].

(* Body *)
Definition body__i_poly_tomsg : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar a_34.(gv) ] _poly_csubq [:: Pvar a_34 ])
    ; MkI dummy_instr_info (Cassgn (Lvar px16.(gv)) AT_none (aarr U16 16) (Pvar hqx16_m1))
    ; MkI dummy_instr_info (Cassgn (Lvar hq.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 px16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar px16.(gv)) AT_none (aarr U16 16) (Pvar hhqx16))
    ; MkI dummy_instr_info (Cassgn (Lvar hhq.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 px16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cfor
                              (i_84.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (256)%Z) (Pconst (32)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar f0_0.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_34 (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pvar i_84))))
                                ; MkI dummy_instr_info (Cassgn (Lvar f1_0.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 a_34 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pvar i_84)) (Pconst (1)%Z))))
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar hq
                                                                    ; Pvar f0_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar hq
                                                                    ; Pvar f1_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRA VE16 U256))))) [:: Pvar f0_0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (15)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRA VE16 U256))))) [:: Pvar f1_0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (15)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPXOR U256))))) [:: Pvar f0_0
                                                                    ; Pvar g0_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPXOR U256))))) [:: Pvar f1_0
                                                                    ; Pvar g1_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar f0_0
                                                                    ; Pvar hhq ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar f1_0
                                                                    ; Pvar hhq ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPACKSS VE16 U256))))) [:: Pvar f0_0
                                                                    ; Pvar f1_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar f0_0
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (216)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar c_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (MOVEMASK VE8 U256))))) [:: Pvar f0_0 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U32 rp_14.(gv) (Pvar i_84)) AT_none (aword U32) (Pvar c_0)) ]) ].

Definition fd__i_poly_tomsg : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__i_poly_tomsg;
    f_params := args__i_poly_tomsg;
    f_body := body__i_poly_tomsg;
    f_tyout := tyout__i_poly_tomsg;
    f_res := res__i_poly_tomsg;
    f_extra := tt;
  |}.

End IDO.
