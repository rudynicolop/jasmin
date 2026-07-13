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

(* __cbd2 *)
(* Local variables *)
Definition rp_6 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14140).
Definition buf_169 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 14141).
Definition mask55_s : gvar := mk_rocq_gvar Slocal (aword U32) (mkident 14142).
Definition mask33_s : gvar := mk_rocq_gvar Slocal (aword U32) (mkident 14143).
Definition mask03_s : gvar := mk_rocq_gvar Slocal (aword U32) (mkident 14144).
Definition mask0F_s : gvar := mk_rocq_gvar Slocal (aword U32) (mkident 14145).
Definition mask55 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14146).
Definition mask33 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14147).
Definition mask03 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14148).
Definition mask0F : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14149).
Definition i_78 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14150).
Definition f0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14151).
Definition f1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14152).
Definition f2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14153).
Definition f3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14154).
Definition t_15 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 14155).

(* Signature *)
Definition tyin___cbd2 : seq atype := [:: aarr U16 256; aarr U8 128 ].
Definition args___cbd2 : seq var_i := [:: rp_6.(gv); buf_169.(gv) ].
Definition tyout___cbd2 : seq atype := [:: aarr U16 256 ].
Definition res___cbd2 : seq var_i := [:: rp_6.(gv) ].

(* Body *)
Definition body___cbd2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar mask55_s.(gv)) AT_none (aword U32) (Papp1 (Oword_of_int U32) (Pconst (1431655765)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar mask33_s.(gv)) AT_none (aword U32) (Papp1 (Oword_of_int U32) (Pconst (858993459)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar mask03_s.(gv)) AT_none (aword U32) (Papp1 (Oword_of_int U32) (Pconst (50529027)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar mask0F_s.(gv)) AT_none (aword U32) (Papp1 (Oword_of_int U32) (Pconst (252645135)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar mask55.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pvar mask55_s ])
    ; MkI dummy_instr_info (Copn [:: Lvar mask33.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pvar mask33_s ])
    ; MkI dummy_instr_info (Copn [:: Lvar mask03.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pvar mask03_s ])
    ; MkI dummy_instr_info (Copn [:: Lvar mask0F.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pvar mask0F_s ])
    ; MkI dummy_instr_info (Cfor
                              (i_78.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (256)%Z) (Pconst (64)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar f0.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 buf_169 (Pvar i_78)))
                                ; MkI dummy_instr_info (Copn [:: Lvar f1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar f0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask55
                                                                    ; Pvar f0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask55
                                                                    ; Pvar f1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE8 U256))))) [:: Pvar f0
                                                                    ; Pvar f1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar f0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (2)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask33
                                                                    ; Pvar f0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask33
                                                                    ; Pvar f1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE8 U256))))) [:: Pvar f0
                                                                    ; Pvar mask33 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE8 U256))))) [:: Pvar f0
                                                                    ; Pvar f1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE16 U256))))) [:: Pvar f0
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (4)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask0F
                                                                    ; Pvar f0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar mask0F
                                                                    ; Pvar f1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE8 U256))))) [:: Pvar f0
                                                                    ; Pvar mask03 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE8 U256))))) [:: Pvar f1
                                                                    ; Pvar mask03 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKL VE8 U256))))) [:: Pvar f0
                                                                    ; Pvar f1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE8 U256))))) [:: Pvar f0
                                                                    ; Pvar f1 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_15.(gv)) AT_none (aword U128) (Pvar f2))
                                ; MkI dummy_instr_info (Copn [:: Lvar f0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMOVSX VE8 U128 VE16 U256))))) [:: Pvar t_15 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t_15.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar f2
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMOVSX VE8 U128 VE16 U256))))) [:: Pvar t_15 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_15.(gv)) AT_none (aword U128) (Pvar f3))
                                ; MkI dummy_instr_info (Copn [:: Lvar f2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMOVSX VE8 U128 VE16 U256))))) [:: Pvar t_15 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar t_15.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar f3
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMOVSX VE8 U128 VE16 U256))))) [:: Pvar t_15 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_6.(gv) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_78))) AT_none (aword U256) (Pvar f0))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_6.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_78)) (Pconst (1)%Z))) AT_none (aword U256) (Pvar f2))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_6.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_78)) (Pconst (2)%Z))) AT_none (aword U256) (Pvar f1))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_6.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_78)) (Pconst (3)%Z))) AT_none (aword U256) (Pvar f3)) ]) ].

Definition fd___cbd2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___cbd2;
    f_params := args___cbd2;
    f_body := body___cbd2;
    f_tyout := tyout___cbd2;
    f_res := res___cbd2;
    f_extra := tt;
  |}.

End IDO.
