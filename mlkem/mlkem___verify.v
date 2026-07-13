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

(* __verify *)
(* Local variables *)
Definition ct_1 : gvar := mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13666).
Definition ctpc : gvar := mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13667).
Definition cnd : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13668).
Definition t64_15 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13669).
Definition h_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13670).
Definition i_99 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13671).
Definition f_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13672).
Definition g : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13673).
Definition zf_34 : gvar := mk_rocq_gvar Slocal (abool) (mkident 13674).

(* Signature *)
Definition tyin___verify : seq atype := [:: aarr U8 1088; aarr U8 1088 ].
Definition args___verify : seq var_i := [:: ct_1.(gv); ctpc.(gv) ].
Definition tyout___verify : seq atype := [:: aword U64 ].
Definition res___verify : seq var_i := [:: cnd.(gv) ].

(* Body *)
Definition body___verify : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar cnd.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar t64_15.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (1)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar h_0.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
    ; MkI dummy_instr_info (Cfor
                              (i_99.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (320)%Z)) (Pconst (128)%Z)) (Pconst (32)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar f_2.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ctpc (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_99))))
                                ; MkI dummy_instr_info (Cassgn (Lvar g.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ct_1 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_99))))
                                ; MkI dummy_instr_info (Copn [:: Lvar f_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPXOR U256))))) [:: Pvar f_2
                                                                    ; Pvar g ])
                                ; MkI dummy_instr_info (Copn [:: Lvar h_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPOR U256))))) [:: Pvar h_0
                                                                    ; Pvar f_2 ]) ])
    ; MkI dummy_instr_info (Copn [:: Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lnone dummy_var_info (abool)
                                   ; Lvar zf_34.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPTEST U256))))) [:: Pvar h_0
                                                                    ; Pvar h_0 ])
    ; MkI dummy_instr_info (Cassgn (Lvar cnd.(gv)) AT_none (aword U64) (Pif (aword U64) (Papp1 (Onot) (Pvar zf_34)) (Pvar t64_15) (Pvar cnd))) ].

Definition fd___verify : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___verify;
    f_params := args___verify;
    f_body := body___verify;
    f_tyout := tyout___verify;
    f_res := res___verify;
    f_extra := tt;
  |}.

End IDO.
