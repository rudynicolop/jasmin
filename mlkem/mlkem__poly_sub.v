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

(* _poly_sub *)
(* Local variables *)
Definition rp_14013 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14013).
Definition ap_14014 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14014).
Definition bp_14015 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14015).
Definition i_14016 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14016).
Definition a_14017 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14017).
Definition b_14018 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14018).
Definition r_14019 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14019).

(* Signature *)
Definition tyin__poly_sub : seq atype :=
  [:: aarr U16 256; aarr U16 256; aarr U16 256 ].
Definition args__poly_sub : seq var_i :=
  [:: rp_14013.(gv); ap_14014.(gv); bp_14015.(gv) ].
Definition tyout__poly_sub : seq atype := [:: aarr U16 256 ].
Definition res__poly_sub : seq var_i := [:: rp_14013.(gv) ].

(* Body *)
Definition body__poly_sub : cmd :=
  [:: MkI dummy_instr_info (Cfor
                              (i_14016.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (16)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar a_14017.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap_14014 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_14016))))
                                ; MkI dummy_instr_info (Cassgn (Lvar b_14018.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_14015 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_14016))))
                                ; MkI dummy_instr_info (Copn [:: Lvar r_14019.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSUB VE16 U256))))) [:: Pvar a_14017
                                                                    ; Pvar b_14018 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_14013.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_14016))) AT_none (aword U256) (Pvar r_14019)) ]) ].

Definition fd__poly_sub : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__poly_sub;
    f_params := args__poly_sub;
    f_body := body__poly_sub;
    f_tyout := tyout__poly_sub;
    f_res := res__poly_sub;
    f_extra := tt;
  |}.

End IDO.
