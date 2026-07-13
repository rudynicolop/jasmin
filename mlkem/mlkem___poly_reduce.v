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

(* __poly_reduce *)
(* Local variables *)
Definition rp_11 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14024).
Definition qx16_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14025).
Definition vx16_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14026).
Definition i_81 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14027).
Definition r_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14028).

(* Signature *)
Definition tyin___poly_reduce : seq atype := [:: aarr U16 256 ].
Definition args___poly_reduce : seq var_i := [:: rp_11.(gv) ].
Definition tyout___poly_reduce : seq atype := [:: aarr U16 256 ].
Definition res___poly_reduce : seq var_i := [:: rp_11.(gv) ].

(* Body *)
Definition body___poly_reduce : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar qx16_12.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jqx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar vx16_2.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jvx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cfor
                              (i_81.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (16)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar r_8.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_11 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_81))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r_8.(gv) ] __red16x [:: Pvar r_8
                                                                    ; Pvar qx16_12
                                                                    ; Pvar vx16_2 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_11.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_81))) AT_none (aword U256) (Pvar r_8)) ]) ].

Definition fd___poly_reduce : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___poly_reduce;
    f_params := args___poly_reduce;
    f_body := body___poly_reduce;
    f_tyout := tyout___poly_reduce;
    f_res := res___poly_reduce;
    f_extra := tt;
  |}.

End IDO.
