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

(* _poly_add2 *)
(* Local variables *)
Definition rp_14265 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14265).
Definition bp : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14266).
Definition i_14267 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14267).
Definition a_14268 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14268).
Definition b_14269 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14269).
Definition r_14270 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14270).

(* Signature *)
Definition tyin__poly_add2 : seq atype := [:: aarr U16 256; aarr U16 256 ].
Definition args__poly_add2 : seq var_i := [:: rp_14265.(gv); bp.(gv) ].
Definition tyout__poly_add2 : seq atype := [:: aarr U16 256 ].
Definition res__poly_add2 : seq var_i := [:: rp_14265.(gv) ].

(* Body *)
Definition body__poly_add2 : cmd :=
  [:: MkI dummy_instr_info (Cfor
                              (i_14267.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (16)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar a_14268.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp_14265 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_14267))))
                                ; MkI dummy_instr_info (Cassgn (Lvar b_14269.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_14267))))
                                ; MkI dummy_instr_info (Copn [:: Lvar r_14270.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPADD VE16 U256))))) [:: Pvar a_14268
                                                                    ; Pvar b_14269 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_14265.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_14267))) AT_none (aword U256) (Pvar r_14270)) ]) ].

Definition fd__poly_add2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__poly_add2;
    f_params := args__poly_add2;
    f_body := body__poly_add2;
    f_tyout := tyout__poly_add2;
    f_res := res__poly_add2;
    f_extra := tt;
  |}.

End IDO.
