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

(* __verify *)
(* Local variables *)
Definition ct_13666 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13666).
Definition ctpc : gvar := mk_rocq_gvar Slocal (aarr U8 1088) (mkident 13667).
Definition cnd : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13668).
Definition t64_13669 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13669).
Definition h_13670 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13670).
Definition i_13671 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13671).
Definition f_13672 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13672).
Definition g : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13673).
Definition zf_13674 : gvar := mk_rocq_gvar Slocal (abool) (mkident 13674).

(* Signature *)
Definition tyin___verify : seq atype := [:: aarr U8 1088; aarr U8 1088 ].
Definition args___verify : seq var_i := [:: ct_13666.(gv); ctpc.(gv) ].
Definition tyout___verify : seq atype := [:: aword U64 ].
Definition res___verify : seq var_i := [:: cnd.(gv) ].

(* Body *)
Definition body___verify : cmd :=
  [:: cassgn (Lvar cnd.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
    ; cassgn (Lvar t64_13669.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (1)%Z))
    ; copn [:: Lvar h_13670.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::]
    ; cfor
        (i_13671.(gv))
        (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (320)%Z)) (Pconst (128)%Z)) (Pconst (32)%Z))
        [:: cassgn (Lvar f_13672.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ctpc (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_13671)))
          ; cassgn (Lvar g.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ct_13666 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_13671)))
          ; copn [:: Lvar f_13672.(gv) ] (Oasm ((BaseOp ((None), (VPXOR U256))))) [:: Pvar f_13672
                                                                    ; Pvar g ]
          ; copn [:: Lvar h_13670.(gv) ] (Oasm ((BaseOp ((None), (VPOR U256))))) [:: Pvar h_13670
                                                                    ; Pvar f_13672 ] ]
    ; copn [:: Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lnone dummy_var_info (abool)
             ; Lvar zf_13674.(gv) ] (Oasm ((BaseOp ((None), (VPTEST U256))))) [:: Pvar h_13670
                                                                    ; Pvar h_13670 ]
    ; cassgn (Lvar cnd.(gv)) (aword U64) (Pif (aword U64) (Papp1 (Onot) (Pvar zf_13674)) (Pvar t64_13669) (Pvar cnd)) ].

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
