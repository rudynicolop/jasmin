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

(* _poly_frommont *)
(* Local variables *)
Definition rp_14177 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14177).
Definition qx16_14178 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14178).
Definition qinvx16_14179 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14179).
Definition dmontx16 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14180).
Definition i_14181 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14181).
Definition t_14182 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14182).

(* Signature *)
Definition tyin__poly_frommont : seq atype := [:: aarr U16 256 ].
Definition args__poly_frommont : seq var_i := [:: rp_14177.(gv) ].
Definition tyout__poly_frommont : seq atype := [:: aarr U16 256 ].
Definition res__poly_frommont : seq var_i := [:: rp_14177.(gv) ].

(* Body *)
Definition body__poly_frommont : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar qx16_14178.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jqx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar qinvx16_14179.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jqinvx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar dmontx16.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jdmontx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cfor
                              (i_14181.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (256)%Z) (Pconst (16)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t_14182.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 rp_14177 (Pvar i_14181)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar t_14182.(gv) ] __fqmulx16 [:: Pvar t_14182
                                                                    ; Pvar dmontx16
                                                                    ; Pvar qx16_14178
                                                                    ; Pvar qinvx16_14179 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_14177.(gv) (Pvar i_14181)) AT_none (aword U256) (Pvar t_14182)) ]) ].

Definition fd__poly_frommont : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__poly_frommont;
    f_params := args__poly_frommont;
    f_body := body__poly_frommont;
    f_tyout := tyout__poly_frommont;
    f_res := res__poly_frommont;
    f_extra := tt;
  |}.

End IDO.
