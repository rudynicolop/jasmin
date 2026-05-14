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

(* __st4x_pack *)
(* Local variables *)
Definition st4x : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18620).
Definition st0 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18621).
Definition st1 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18622).
Definition st2 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18623).
Definition st3_18624 : gvar :=
  mk_rocq_gvar Slocal (aarr U64 25) (mkident 18624).
Definition i_18625 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18625).
Definition x0_18626 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18626).
Definition x1_18627 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18627).
Definition x2_18628 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18628).
Definition x3_18629 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18629).
Definition t0_18630 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18630).
Definition t1_18631 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18631).
Definition t2_18632 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18632).
Definition t3_18633 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18633).

(* Signature *)
Definition tyin___st4x_pack : seq atype :=
  [:: aarr U256 25; aarr U64 25; aarr U64 25; aarr U64 25; aarr U64 25 ].
Definition args___st4x_pack : seq var_i :=
  [:: st4x.(gv); st0.(gv); st1.(gv); st2.(gv); st3_18624.(gv) ].
Definition tyout___st4x_pack : seq atype := [:: aarr U256 25 ].
Definition res___st4x_pack : seq var_i := [:: st4x.(gv) ].

(* Body *)
Definition body___st4x_pack : cmd :=
  [:: MkI dummy_instr_info (Cfor
                              (i_18625.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (6)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_18626.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st0 (Pvar i_18625)))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_18627.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st1 (Pvar i_18625)))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_18628.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st2 (Pvar i_18625)))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_18629.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st3_18624 (Pvar i_18625)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_18626.(gv)
                                                                ; Lvar x1_18627.(gv)
                                                                ; Lvar x2_18628.(gv)
                                                                ; Lvar x3_18629.(gv) ] __u256x4_4u64x4 [:: Pvar x0_18626
                                                                    ; Pvar x1_18627
                                                                    ; Pvar x2_18628
                                                                    ; Pvar x3_18629 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_18625)) (Pconst (0)%Z))) AT_none (aword U256) (Pvar x0_18626))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_18625)) (Pconst (1)%Z))) AT_none (aword U256) (Pvar x1_18627))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_18625)) (Pconst (2)%Z))) AT_none (aword U256) (Pvar x2_18628))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_18625)) (Pconst (3)%Z))) AT_none (aword U256) (Pvar x3_18629)) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t0_18630.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st0 (Pconst (24)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar t1_18631.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st1 (Pconst (24)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar t2_18632.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st2 (Pconst (24)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar t3_18633.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st3_18624 (Pconst (24)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (0)%Z))) AT_none (aword U64) (Pvar t0_18630))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (1)%Z))) AT_none (aword U64) (Pvar t1_18631))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (2)%Z))) AT_none (aword U64) (Pvar t2_18632))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (3)%Z))) AT_none (aword U64) (Pvar t3_18633)) ].

Definition fd___st4x_pack : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___st4x_pack;
    f_params := args___st4x_pack;
    f_body := body___st4x_pack;
    f_tyout := tyout___st4x_pack;
    f_res := res___st4x_pack;
    f_extra := tt;
  |}.

End IDO.
