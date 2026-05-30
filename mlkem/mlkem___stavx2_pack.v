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

(* __stavx2_pack *)
(* Local variables *)
Definition st : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 19007).
Definition state_2 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 19008).
Definition t128_1 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 19009).
Definition t128_0 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 19010).
Definition r_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 19011).
Definition t256_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19012).
Definition t256_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19013).
Definition t256_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19014).

(* Signature *)
Definition tyin___stavx2_pack : seq atype := [:: aarr U64 25 ].
Definition args___stavx2_pack : seq var_i := [:: st.(gv) ].
Definition tyout___stavx2_pack : seq atype := [:: aarr U256 7 ].
Definition res___stavx2_pack : seq var_i := [:: state_2.(gv) ].

(* Body *)
Definition body___stavx2_pack : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state_2.(gv) (Pconst (0)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 st (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pconst (0)%Z)) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state_2.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t128_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VMOV U64))))) [:: Pget Aligned AAscale U64 st (Pconst (5)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state_2.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st (Papp2 (Omul (Op_int)) (Pconst (6)%Z) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t128_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VMOV U64))))) [:: Pget Aligned AAscale U64 st (Pconst (10)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state_2.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st (Papp2 (Omul (Op_int)) (Pconst (11)%Z) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r_5.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st (Pconst (15)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar t128_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1
                                                                    ; Pvar r_5
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state_2.(gv) (Pconst (5)%Z)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st (Papp2 (Omul (Op_int)) (Pconst (16)%Z) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r_5.(gv)) AT_none (aword U64) (Pget Aligned AAscale U64 st (Pconst (20)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar t128_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_0
                                                                    ; Pvar r_5
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t256_0.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_0)))
    ; MkI dummy_instr_info (Copn [:: Lvar t256_0.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar t256_0
                                                                    ; Pvar t128_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state_2.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Pvar t256_0))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 state_2.(gv) (Pconst (6)%Z)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st (Papp2 (Omul (Op_int)) (Pconst (21)%Z) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t256_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state_2 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 state_2 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state_2 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 state_2 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_2.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state_2 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 state_2 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state_2.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0
                                                                    ; Pvar t256_1
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state_2.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1
                                                                    ; Pvar t256_0
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state_2 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 state_2 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state_2.(gv) (Pconst (5)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0
                                                                    ; Pvar t256_2
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 state_2.(gv) (Pconst (6)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2
                                                                    ; Pvar t256_0
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]) ].

Definition fd___stavx2_pack : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___stavx2_pack;
    f_params := args___stavx2_pack;
    f_body := body___stavx2_pack;
    f_tyout := tyout___stavx2_pack;
    f_res := res___stavx2_pack;
    f_extra := tt;
  |}.

End IDO.
