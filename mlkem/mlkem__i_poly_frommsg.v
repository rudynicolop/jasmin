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

(* _i_poly_frommsg *)
(* Local variables *)
Definition rp_5 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14159).
Definition ap_1 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 14160).
Definition hqs : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14161).
Definition shift : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14162).
Definition idx : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14163).
Definition f : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14164).
Definition i_77 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14165).
Definition g3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14166).
Definition g0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14167).
Definition g1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14168).
Definition g2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14169).
Definition h0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14170).
Definition h2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14171).
Definition h1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14172).
Definition h3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14173).

(* Signature *)
Definition tyin__i_poly_frommsg : seq atype := [:: aarr U16 256; aarr U8 32 ].
Definition args__i_poly_frommsg : seq var_i := [:: rp_5.(gv); ap_1.(gv) ].
Definition tyout__i_poly_frommsg : seq atype := [:: aarr U16 256 ].
Definition res__i_poly_frommsg : seq var_i := [:: rp_5.(gv) ].

(* Body *)
Definition body__i_poly_frommsg : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar hqs.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 hqx16_p1 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar shift.(gv) ] AT_none (Oasm ((BaseOp ((None), VBROADCASTI128)))) [:: Pget Aligned AAscale U128 pfm_shift_s (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar idx.(gv) ] AT_none (Oasm ((BaseOp ((None), VBROADCASTI128)))) [:: Pget Aligned AAscale U128 pfm_idx_s (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar f.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 ap_1 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cfor
                              (i_77.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (4)%Z)
                              [:: MkI dummy_instr_info (Copn [:: Lvar g3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSHUFD U256))))) [:: Pvar f
                                                                    ; Papp1 (Oword_of_int U8) (Papp2 (Omul (Op_int)) (Pconst (85)%Z) (Pvar i_77)) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLLV VE32 U256))))) [:: Pvar g3
                                                                    ; Pvar shift ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar g3
                                                                    ; Pvar idx ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar g3
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (12)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar g3
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (8)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE16 U256))))) [:: Pvar g3
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRA VE16 U256))))) [:: Pvar g0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (15)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRA VE16 U256))))) [:: Pvar g1
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (15)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRA VE16 U256))))) [:: Pvar g2
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (15)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRA VE16 U256))))) [:: Pvar g3
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (15)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar g0
                                                                    ; Pvar hqs ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar g1
                                                                    ; Pvar hqs ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar g2
                                                                    ; Pvar hqs ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar g3
                                                                    ; Pvar hqs ])
                                ; MkI dummy_instr_info (Copn [:: Lvar h0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE64 U256))))) [:: Pvar g0
                                                                    ; Pvar g1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar h2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U256))))) [:: Pvar g0
                                                                    ; Pvar g1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar h1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE64 U256))))) [:: Pvar g2
                                                                    ; Pvar g3 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar h3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U256))))) [:: Pvar g2
                                                                    ; Pvar g3 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g0.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar h0
                                                                    ; Pvar h1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (32)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g2.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar h0
                                                                    ; Pvar h1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (49)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g1.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar h2
                                                                    ; Pvar h3
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (32)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar g3.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERM2I128)))) [:: Pvar h2
                                                                    ; Pvar h3
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (49)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_5.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pvar i_77))) AT_none (aword U256) (Pvar g0))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_5.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pvar i_77)) (Pconst (1)%Z))) AT_none (aword U256) (Pvar g1))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_5.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pvar i_77)) (Pconst (8)%Z))) AT_none (aword U256) (Pvar g2))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_5.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pvar i_77)) (Pconst (8)%Z)) (Pconst (1)%Z))) AT_none (aword U256) (Pvar g3)) ]) ].

Definition fd__i_poly_frommsg : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__i_poly_frommsg;
    f_params := args__i_poly_frommsg;
    f_body := body__i_poly_frommsg;
    f_tyout := tyout__i_poly_frommsg;
    f_res := res__i_poly_frommsg;
    f_extra := tt;
  |}.

End IDO.
