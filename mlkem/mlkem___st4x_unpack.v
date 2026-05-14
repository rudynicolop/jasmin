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
Definition st0_18589 : gvar :=
  mk_rocq_gvar Slocal (aarr U64 25) (mkident 18589).
Definition st1_18590 : gvar :=
  mk_rocq_gvar Slocal (aarr U64 25) (mkident 18590).
Definition st2_18591 : gvar :=
  mk_rocq_gvar Slocal (aarr U64 25) (mkident 18591).
Definition st3_18592 : gvar :=
  mk_rocq_gvar Slocal (aarr U64 25) (mkident 18592).
Definition st4x_18593 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18593).
Definition i_18594 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18594).
Definition x0_18595 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18595).
Definition x1_18596 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18596).
Definition x2_18597 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18597).
Definition x3_18598 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18598).
Definition t0_18599 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18599).
Definition t1_18600 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18600).
Definition t2_18601 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18601).
Definition t3_18602 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18602).

(* Signature *)
Definition tyin___st4x_unpack : seq atype :=
  [:: aarr U64 25; aarr U64 25; aarr U64 25; aarr U64 25; aarr U256 25 ].
Definition args___st4x_unpack : seq var_i :=
  [:: st0_18589.(gv)
    ; st1_18590.(gv)
    ; st2_18591.(gv)
    ; st3_18592.(gv)
    ; st4x_18593.(gv) ].
Definition tyout___st4x_unpack : seq atype :=
  [:: aarr U64 25; aarr U64 25; aarr U64 25; aarr U64 25 ].
Definition res___st4x_unpack : seq var_i :=
  [:: st0_18589.(gv); st1_18590.(gv); st2_18591.(gv); st3_18592.(gv) ].

(* Body *)
Definition body___st4x_unpack : cmd :=
  [:: MkI dummy_instr_info (Cfor
                              (i_18594.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (6)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_18595.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st4x_18593 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_18594)) (Pconst (0)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_18596.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st4x_18593 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_18594)) (Pconst (1)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_18597.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st4x_18593 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_18594)) (Pconst (2)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_18598.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 st4x_18593 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_18594)) (Pconst (3)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_18595.(gv)
                                                                ; Lvar x1_18596.(gv)
                                                                ; Lvar x2_18597.(gv)
                                                                ; Lvar x3_18598.(gv) ] __4u64x4_u256x4 [:: Pvar x0_18595
                                                                    ; Pvar x1_18596
                                                                    ; Pvar x2_18597
                                                                    ; Pvar x3_18598 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st0_18589.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (8)%Z)) (Pvar i_18594))) AT_none (aword U256) (Pvar x0_18595))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st1_18590.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (8)%Z)) (Pvar i_18594))) AT_none (aword U256) (Pvar x1_18596))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st2_18591.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (8)%Z)) (Pvar i_18594))) AT_none (aword U256) (Pvar x2_18597))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st3_18592.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (8)%Z)) (Pvar i_18594))) AT_none (aword U256) (Pvar x3_18598)) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t0_18599.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st4x_18593 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar t1_18600.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st4x_18593 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar t2_18601.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st4x_18593 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar t3_18602.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st4x_18593 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pconst (24)%Z)) (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st0_18589.(gv) (Pconst (24)%Z)) AT_none (aword U64) (Pvar t0_18599))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st1_18590.(gv) (Pconst (24)%Z)) AT_none (aword U64) (Pvar t1_18600))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st2_18591.(gv) (Pconst (24)%Z)) AT_none (aword U64) (Pvar t2_18601))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st3_18592.(gv) (Pconst (24)%Z)) AT_none (aword U64) (Pvar t3_18602)) ].

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
