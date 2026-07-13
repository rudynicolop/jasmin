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

(* _poly_csubq *)
(* Local variables *)
Definition rp_1 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14261).
Definition qx16_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14262).
Definition i_74 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14263).
Definition r_7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14264).

(* Signature *)
Definition tyin__poly_csubq : seq atype := [:: aarr U16 256 ].
Definition args__poly_csubq : seq var_i := [:: rp_1.(gv) ].
Definition tyout__poly_csubq : seq atype := [:: aarr U16 256 ].
Definition res__poly_csubq : seq var_i := [:: rp_1.(gv) ].

(* Body *)
Definition body__poly_csubq : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar qx16_3.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jqx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cfor
                              (i_74.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (16)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar r_7.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_1 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_74))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar r_7.(gv) ] __csubq [:: Pvar r_7
                                                                    ; Pvar qx16_3 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_1.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_74))) AT_none (aword U256) (Pvar r_7)) ]) ].

Definition fd__poly_csubq : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__poly_csubq;
    f_params := args__poly_csubq;
    f_body := body__poly_csubq;
    f_tyout := tyout__poly_csubq;
    f_res := res__poly_csubq;
    f_extra := tt;
  |}.

End IDO.
