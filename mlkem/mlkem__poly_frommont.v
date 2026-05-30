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
Definition rp_4 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14177).
Definition qx16_7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14178).
Definition qinvx16_3 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14179).
Definition dmontx16 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14180).
Definition i_76 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14181).
Definition t_14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14182).

(* Signature *)
Definition tyin__poly_frommont : seq atype := [:: aarr U16 256 ].
Definition args__poly_frommont : seq var_i := [:: rp_4.(gv) ].
Definition tyout__poly_frommont : seq atype := [:: aarr U16 256 ].
Definition res__poly_frommont : seq var_i := [:: rp_4.(gv) ].

(* Body *)
Definition body__poly_frommont : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar qx16_7.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jqx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar qinvx16_3.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jqinvx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar dmontx16.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 jdmontx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cfor
                              (i_76.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (256)%Z) (Pconst (16)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t_14.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 rp_4 (Pvar i_76)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar t_14.(gv) ] __fqmulx16 [:: Pvar t_14
                                                                    ; Pvar dmontx16
                                                                    ; Pvar qx16_7
                                                                    ; Pvar qinvx16_3 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_4.(gv) (Pvar i_76)) AT_none (aword U256) (Pvar t_14)) ]) ].

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
