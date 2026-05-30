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

(* __st4x_unpack *)
(* Local variables *)
Definition st0_0 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18589).
Definition st1_0 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18590).
Definition st2_0 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18591).
Definition st3_2 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18592).
Definition st4x_0 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18593).
Definition i_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18594).
Definition x0_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18595).
Definition x1_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18596).
Definition x2_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18597).
Definition x3_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18598).
Definition t0_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18599).
Definition t1_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18600).
Definition t2_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18601).
Definition t3_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18602).

(* Signature *)
Definition tyin___st4x_unpack : seq atype :=
  [:: aarr U64 25; aarr U64 25; aarr U64 25; aarr U64 25; aarr U256 25 ].
Definition args___st4x_unpack : seq var_i :=
  [:: st0_0.(gv); st1_0.(gv); st2_0.(gv); st3_2.(gv); st4x_0.(gv) ].
Definition tyout___st4x_unpack : seq atype :=
  [:: aarr U64 25; aarr U64 25; aarr U64 25; aarr U64 25 ].
Definition res___st4x_unpack : seq var_i :=
  [:: st0_0.(gv); st1_0.(gv); st2_0.(gv); st3_2.(gv) ].

(* Body *)
Definition body___st4x_unpack : cmd :=
  [:: MkI dummy_instr_info (Cfor
                              (i_5.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (6)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_2.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st4x_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_5)) (Pconst (0)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_2.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st4x_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_5)) (Pconst (1)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_2.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st4x_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_5)) (Pconst (2)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_2.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st4x_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_5)) (Pconst (3)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_2.(gv)
                                                                ; Lvar x1_2.(gv)
                                                                ; Lvar x2_2.(gv)
                                                                ; Lvar x3_2.(gv) ] __4u64x4_u256x4 [:: Pvar x0_2
                                                                    ; Pvar x1_2
                                                                    ; Pvar x2_2
                                                                    ; Pvar x3_2 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st0_0.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (8)%Z)) (Pvar i_5))) AT_none (aword U256) (Pvar x0_2))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st1_0.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (8)%Z)) (Pvar i_5))) AT_none (aword U256) (Pvar x1_2))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st2_0.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (8)%Z)) (Pvar i_5))) AT_none (aword U256) (Pvar x2_2))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st3_2.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (8)%Z)) (Pvar i_5))) AT_none (aword U256) (Pvar x3_2)) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t0_3.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st4x_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar t1_3.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st4x_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar t2_1.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st4x_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar t3_1.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st4x_0 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st0_0.(gv) (Pconst (24)%Z)) AT_none (aword U64) (Pvar t0_3))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st1_0.(gv) (Pconst (24)%Z)) AT_none (aword U64) (Pvar t1_3))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st2_0.(gv) (Pconst (24)%Z)) AT_none (aword U64) (Pvar t2_1))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st3_2.(gv) (Pconst (24)%Z)) AT_none (aword U64) (Pvar t3_1)) ].

Definition fd___st4x_unpack : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___st4x_unpack;
    f_params := args___st4x_unpack;
    f_body := body___st4x_unpack;
    f_tyout := tyout___st4x_unpack;
    f_res := res___st4x_unpack;
    f_extra := tt;
  |}.

End IDO.
