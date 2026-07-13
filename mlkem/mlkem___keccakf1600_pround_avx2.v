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

(* __keccakf1600_pround_avx2 *)
(* Local variables *)
Definition state : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 19020).
Definition c00 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19021).
Definition c14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19022).
Definition t2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19023).
Definition t4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19024).
Definition t0_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19025).
Definition t1_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19026).
Definition d14 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19027).
Definition d00 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19028).
Definition t3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19029).
Definition t5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19030).
Definition t6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19031).
Definition t7 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19032).
Definition t8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19033).

(* Signature *)
Definition tyin___keccakf1600_pround_avx2 : seq atype := [:: aarr U256 7 ].
Definition args___keccakf1600_pround_avx2 : seq var_i := [:: state.(gv) ].
Definition tyout___keccakf1600_pround_avx2 : seq atype := [:: aarr U256 7 ].
Definition res___keccakf1600_pround_avx2 : seq var_i := [:: state.(gv) ].

(* Body *)
Definition body___keccakf1600_pround_avx2 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar c00.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSHUFD U256))))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (2)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Lvar c14.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (5)%Z)) (Pget Aligned AAscale U256 state (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar t2.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (4)%Z)) (Pget Aligned AAscale U256 state (Pconst (6)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar c14.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar c14) (Pget Aligned AAscale U256 state (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar c14.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar c14) (Pvar t2)))
    ; MkI dummy_instr_info (Copn [:: Lvar t4.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar c14
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (2)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (3)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Lvar c00.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar c00) (Pget Aligned AAscale U256 state (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar c00
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (2)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Lvar t1_1.(gv)) AT_none (aword U256) (Papp2 (Ovlsr VE64 U256) (Pvar c14) (Papp1 (Oword_of_int U128) (Pconst (63)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar t2.(gv)) AT_none (aword U256) (Papp2 (Ovadd VE64 U256) (Pvar c14) (Pvar c14)))
    ; MkI dummy_instr_info (Cassgn (Lvar t1_1.(gv)) AT_none (aword U256) (Papp2 (Olor U256) (Pvar t1_1) (Pvar t2)))
    ; MkI dummy_instr_info (Copn [:: Lvar d14.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar t1_1
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (2)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Lvar d00.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t1_1) (Pvar t4)))
    ; MkI dummy_instr_info (Copn [:: Lvar d00.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar d00
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Lvar c00.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar c00) (Pget Aligned AAscale U256 state (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar c00.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar c00) (Pvar t0_1)))
    ; MkI dummy_instr_info (Cassgn (Lvar t0_1.(gv)) AT_none (aword U256) (Papp2 (Ovlsr VE64 U256) (Pvar c00) (Papp1 (Oword_of_int U128) (Pconst (63)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar t1_1.(gv)) AT_none (aword U256) (Papp2 (Ovadd VE64 U256) (Pvar c00) (Pvar c00)))
    ; MkI dummy_instr_info (Cassgn (Lvar t1_1.(gv)) AT_none (aword U256) (Papp2 (Olor U256) (Pvar t1_1) (Pvar t0_1)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (2)%Z)) (Pvar d00)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (0)%Z)) (Pvar d00)))
    ; MkI dummy_instr_info (Copn [:: Lvar d14.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar d14
                                                                    ; Pvar t1_1
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t4
                                                                    ; Pvar c00
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Lvar d14.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar d14) (Pvar t4)))
    ; MkI dummy_instr_info (Copn [:: Lvar t3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 state (Pconst (2)%Z)) (Pvar t3)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (3)%Z)) (Pvar d14)))
    ; MkI dummy_instr_info (Copn [:: Lvar t4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (2)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (2)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 state (Pconst (3)%Z)) (Pvar t4)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (4)%Z)) (Pvar d14)))
    ; MkI dummy_instr_info (Copn [:: Lvar t5.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (3)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (3)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 state (Pconst (4)%Z)) (Pvar t5)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (5)%Z)) (Pvar d14)))
    ; MkI dummy_instr_info (Copn [:: Lvar t6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (4)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (4)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 state (Pconst (5)%Z)) (Pvar t6)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (6)%Z)) (Pvar d14)))
    ; MkI dummy_instr_info (Copn [:: Lvar t3.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (2)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t4.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (2)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (5)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar t1_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (5)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t1_1.(gv)) AT_none (aword U256) (Papp2 (Olor U256) (Pvar t1_1) (Pvar t7)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (1)%Z)) (Pvar d14)))
    ; MkI dummy_instr_info (Copn [:: Lvar t5.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (2)%Z
                                                                    ; Pconst (3)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t6.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (1)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (2)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar t2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t2.(gv)) AT_none (aword U256) (Papp2 (Olor U256) (Pvar t2) (Pvar t8)))
    ; MkI dummy_instr_info (Copn [:: Lvar t7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRLDQ U256))))) [:: Pvar t1_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (8)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t0_1.(gv)) AT_none (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pvar t1_1)) (Pvar t7)))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t2
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t4
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t3
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t2
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t8
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t8
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (3)%Z))) (Pvar t8)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z)) AT_none (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (5)%Z))) (Pvar t7)))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t5
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t3
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (3)%Z)) (Pvar t3)))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (6)%Z)
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t8
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (5)%Z)) (Pvar t5)))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (6)%Z)
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t8
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z)) AT_none (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (6)%Z))) (Pvar t8)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (6)%Z)) (Pvar t6)))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar t1_1
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (2)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 state (Pconst (0)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (1)%Z) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar t1_1
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (2)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (1)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 state (Pconst (0)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (1)%Z))) (Pvar t8)))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t4
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t6
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (2)%Z))) (Pvar t7)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (2)%Z)) (Pvar t2)))
    ; MkI dummy_instr_info (Copn [:: Lvar t0_1.(gv) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar t0_1
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (2)%Z
                                                                    ; Pconst (3)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (2)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z) ] AT_none (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (1)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (2)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t6
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t5
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t7.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (4)%Z))) (Pvar t7)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (0)%Z)) (Pvar t0_1)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (1)%Z)) (Pvar t1_1)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (4)%Z)) (Pvar t4))) ].

Definition fd___keccakf1600_pround_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___keccakf1600_pround_avx2;
    f_params := args___keccakf1600_pround_avx2;
    f_body := body___keccakf1600_pround_avx2;
    f_tyout := tyout___keccakf1600_pround_avx2;
    f_res := res___keccakf1600_pround_avx2;
    f_extra := tt;
  |}.

End IDO.
