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
Definition st3_1 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18624).
Definition i_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18625).
Definition x0_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18626).
Definition x1_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18627).
Definition x2_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18628).
Definition x3_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18629).
Definition t0_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18630).
Definition t1_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18631).
Definition t2_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18632).
Definition t3_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18633).

(* Signature *)
Definition tyin___st4x_pack : seq atype :=
  [:: aarr U256 25; aarr U64 25; aarr U64 25; aarr U64 25; aarr U64 25 ].
Definition args___st4x_pack : seq var_i :=
  [:: st4x.(gv); st0.(gv); st1.(gv); st2.(gv); st3_1.(gv) ].
Definition tyout___st4x_pack : seq atype := [:: aarr U256 25 ].
Definition res___st4x_pack : seq var_i := [:: st4x.(gv) ].

(* Body *)
Definition body___st4x_pack : cmd :=
  [:: MkI dummy_instr_info (Cfor
                              (i_4.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (6)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_0.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st0 (Pvar i_4)))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_0.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st1 (Pvar i_4)))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_0.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st2 (Pvar i_4)))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_0.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st3_1 (Pvar i_4)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_0.(gv)
                                                                ; Lvar x1_0.(gv)
                                                                ; Lvar x2_0.(gv)
                                                                ; Lvar x3_0.(gv) ] __u256x4_4u64x4 [:: Pvar x0_0
                                                                    ; Pvar x1_0
                                                                    ; Pvar x2_0
                                                                    ; Pvar x3_0 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_4)) (Pconst (0)%Z))) AT_none (aword U256) (Pvar x0_0))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_4)) (Pconst (1)%Z))) AT_none (aword U256) (Pvar x1_0))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_4)) (Pconst (2)%Z))) AT_none (aword U256) (Pvar x2_0))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_4)) (Pconst (3)%Z))) AT_none (aword U256) (Pvar x3_0)) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t0_2.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st0 (Pconst (24)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar t1_2.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st1 (Pconst (24)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar t2_0.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st2 (Pconst (24)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar t3_0.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st3_1 (Pconst (24)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (0)%Z))) AT_none (aword U64) (Pvar t0_2))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (1)%Z))) AT_none (aword U64) (Pvar t1_2))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (2)%Z))) AT_none (aword U64) (Pvar t2_0))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st4x.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (3)%Z))) AT_none (aword U64) (Pvar t3_0)) ].

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
