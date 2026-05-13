From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

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
Definition t0_19025 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19025).
Definition t1_19026 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19026).
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
  [:: copn [:: Lvar c00.(gv) ] (Oasm ((BaseOp ((None), (VPSHUFD U256))))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                    ; PappN (Opack U8 PE2) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (2)%Z ] ]
    ; cassgn (Lvar c14.(gv)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (5)%Z)) (Pget Aligned AAscale U256 state (Pconst (3)%Z)))
    ; cassgn (Lvar t2.(gv)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (4)%Z)) (Pget Aligned AAscale U256 state (Pconst (6)%Z)))
    ; cassgn (Lvar c14.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar c14) (Pget Aligned AAscale U256 state (Pconst (1)%Z)))
    ; cassgn (Lvar c14.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar c14) (Pvar t2))
    ; copn [:: Lvar t4.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar c14
                                                                   ; PappN (Opack U8 PE2) 
                                                                 [:: Pconst (2)%Z
                                                                   ; Pconst (1)%Z
                                                                   ; Pconst (0)%Z
                                                                   ; Pconst (3)%Z ] ]
    ; cassgn (Lvar c00.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar c00) (Pget Aligned AAscale U256 state (Pconst (2)%Z)))
    ; copn [:: Lvar t0_19025.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar c00
                                                                    ; PappN (Opack U8 PE2) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (2)%Z ] ]
    ; cassgn (Lvar t1_19026.(gv)) (aword U256) (Papp2 (Ovlsr VE64 U256) (Pvar c14) (Papp1 (Oword_of_int U128) (Pconst (63)%Z)))
    ; cassgn (Lvar t2.(gv)) (aword U256) (Papp2 (Ovadd VE64 U256) (Pvar c14) (Pvar c14))
    ; cassgn (Lvar t1_19026.(gv)) (aword U256) (Papp2 (Olor U256) (Pvar t1_19026) (Pvar t2))
    ; copn [:: Lvar d14.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar t1_19026
                                                                    ; PappN (Opack U8 PE2) 
                                                                  [:: Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (2)%Z
                                                                    ; Pconst (1)%Z ] ]
    ; cassgn (Lvar d00.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t1_19026) (Pvar t4))
    ; copn [:: Lvar d00.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar d00
                                                                    ; PappN (Opack U8 PE2) 
                                                                  [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; cassgn (Lvar c00.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar c00) (Pget Aligned AAscale U256 state (Pconst (0)%Z)))
    ; cassgn (Lvar c00.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar c00) (Pvar t0_19025))
    ; cassgn (Lvar t0_19025.(gv)) (aword U256) (Papp2 (Ovlsr VE64 U256) (Pvar c00) (Papp1 (Oword_of_int U128) (Pconst (63)%Z)))
    ; cassgn (Lvar t1_19026.(gv)) (aword U256) (Papp2 (Ovadd VE64 U256) (Pvar c00) (Pvar c00))
    ; cassgn (Lvar t1_19026.(gv)) (aword U256) (Papp2 (Olor U256) (Pvar t1_19026) (Pvar t0_19025))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (2)%Z)) (Pvar d00))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (0)%Z)) (Pvar d00))
    ; copn [:: Lvar d14.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar d14
                                                                    ; Pvar t1_19026
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t4.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t4
                                                                    ; Pvar c00
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
    ; cassgn (Lvar d14.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar d14) (Pvar t4))
    ; copn [:: Lvar t3.(gv) ] (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (0)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z) ] (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (0)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 state (Pconst (2)%Z)) (Pvar t3))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (3)%Z)) (Pvar d14))
    ; copn [:: Lvar t4.(gv) ] (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (2)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z) ] (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (2)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 state (Pconst (3)%Z)) (Pvar t4))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (4)%Z)) (Pvar d14))
    ; copn [:: Lvar t5.(gv) ] (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (3)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z) ] (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (3)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 state (Pconst (4)%Z)) (Pvar t5))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (5)%Z)) (Pvar d14))
    ; copn [:: Lvar t6.(gv) ] (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (4)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z) ] (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (4)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 state (Pconst (5)%Z)) (Pvar t6))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (6)%Z)) (Pvar d14))
    ; copn [:: Lvar t3.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                   ; PappN (Opack U8 PE2) 
                                                                 [:: Pconst (2)%Z
                                                                   ; Pconst (0)%Z
                                                                   ; Pconst (3)%Z
                                                                   ; Pconst (1)%Z ] ]
    ; copn [:: Lvar t4.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                   ; PappN (Opack U8 PE2) 
                                                                 [:: Pconst (2)%Z
                                                                   ; Pconst (0)%Z
                                                                   ; Pconst (3)%Z
                                                                   ; Pconst (1)%Z ] ]
    ; copn [:: Lvar t7.(gv) ] (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (5)%Z) ]
    ; copn [:: Lvar t1_19026.(gv) ] (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (5)%Z) ]
    ; cassgn (Lvar t1_19026.(gv)) (aword U256) (Papp2 (Olor U256) (Pvar t1_19026) (Pvar t7))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (1)%Z)) (Pvar d14))
    ; copn [:: Lvar t5.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                   ; PappN (Opack U8 PE2) 
                                                                 [:: Pconst (0)%Z
                                                                   ; Pconst (1)%Z
                                                                   ; Pconst (2)%Z
                                                                   ; Pconst (3)%Z ] ]
    ; copn [:: Lvar t6.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                   ; PappN (Opack U8 PE2) 
                                                                 [:: Pconst (1)%Z
                                                                   ; Pconst (3)%Z
                                                                   ; Pconst (0)%Z
                                                                   ; Pconst (2)%Z ] ]
    ; copn [:: Lvar t8.(gv) ] (Oasm ((BaseOp ((None), (VPSLLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_LEFT (Pconst (1)%Z) ]
    ; copn [:: Lvar t2.(gv) ] (Oasm ((BaseOp ((None), (VPSRLV VE64 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 KECCAK_RHOTATES_RIGHT (Pconst (1)%Z) ]
    ; cassgn (Lvar t2.(gv)) (aword U256) (Papp2 (Olor U256) (Pvar t2) (Pvar t8))
    ; copn [:: Lvar t7.(gv) ] (Oasm ((BaseOp ((None), (VPSRLDQ U256))))) [:: Pvar t1_19026
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (8)%Z) ]
    ; cassgn (Lvar t0_19025.(gv)) (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pvar t1_19026)) (Pvar t7))
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t2
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t8.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t4
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t3
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t7.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t2
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t8.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t8
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t7.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t8.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t8
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t7.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (3)%Z))) (Pvar t8))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z)) (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (5)%Z))) (Pvar t7))
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t5
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t8.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t3
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (3)%Z)) (Pvar t3))
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (6)%Z)
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t8.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t8
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (5)%Z)) (Pvar t5))
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (6)%Z)
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t8.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t8
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z)) (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (6)%Z))) (Pvar t8))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (6)%Z)) (Pvar t6))
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar t1_19026
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (2)%Z ] ]
    ; copn [:: Lvar t8.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 state (Pconst (0)%Z)
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (1)%Z) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar t1_19026
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (2)%Z
                                                                    ; Pconst (1)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (1)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 state (Pconst (0)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (1)%Z))) (Pvar t8))
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t4
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t7.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t6
                                                                    ; Pvar t4
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t7.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (2)%Z)
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t7.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (2)%Z))) (Pvar t7))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (2)%Z)) (Pvar t2))
    ; copn [:: Lvar t0_19025.(gv) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pvar t0_19025
                                                                    ; PappN (Opack U8 PE2) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (3)%Z) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (2)%Z
                                                                    ; Pconst (3)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (5)%Z) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (2)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (1)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (6)%Z) ] (Oasm ((BaseOp ((None), VPERMQ)))) [:: Pget Aligned AAscale U256 state (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE2) [:: Pconst (1)%Z
                                                                    ; Pconst (3)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (2)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t6
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t7.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t5
                                                                    ; Pvar t6
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                    ; Pvar t5
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t7.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state (Pconst (4)%Z)
                                                                    ; Pvar t2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; copn [:: Lvar t7.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t7
                                                                    ; Pvar t3
                                                                    ; PappN (Opack U8 PE1) 
                                                                    [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Oland U256) (Papp1 (Olnot U256) (Pget Aligned AAscale U256 state (Pconst (4)%Z))) (Pvar t7))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (0)%Z)) (Pvar t0_19025))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (1)%Z)) (Pvar t1_19026))
    ; cassgn (Laset Aligned AAscale U256 state.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state (Pconst (4)%Z)) (Pvar t4)) ].

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
