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

(* __stavx2_unpack *)
(* Local variables *)
Definition st_0 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18995).
Definition state_3 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 18996).
Definition t128_0_0 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18997).
Definition t256_0_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18998).
Definition t256_1_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18999).
Definition t256_2_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19000).
Definition t256_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19001).
Definition t128_1_0 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 19002).
Definition t256_4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19003).

(* Signature *)
Definition tyin___stavx2_unpack : seq atype := [:: aarr U64 25; aarr U256 7 ].
Definition args___stavx2_unpack : seq var_i := [:: st_0.(gv); state_3.(gv) ].
Definition tyout___stavx2_unpack : seq atype := [:: aarr U64 25 ].
Definition res___stavx2_unpack : seq var_i := [:: st_0.(gv) ].

(* Body *)
Definition body___stavx2_unpack : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar t128_0_0.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 state_3 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U64 st_0.(gv) (Pconst (0)%Z) ] AT_none (Oasm ((BaseOp ((None), VMOVLPD)))) [:: Pvar t128_0_0 ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_0.(gv) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))) AT_none (aword U256) (Pget Aligned AAscale U256 state_3 (Pconst (1)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar t256_0_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state_3 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 state_3 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state_3 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 state_3 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_2_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state_3 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 state_3 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 state_3 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 state_3 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ])
    ; MkI dummy_instr_info (Copn [:: Lvar t128_1_0.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 state_3 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U64 st_0.(gv) (Pconst (5)%Z) ] AT_none (Oasm ((BaseOp ((None), VMOVLPD)))) [:: Pvar t128_1_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_0
                                                                    ; Pvar t256_3
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_0.(gv) (Papp2 (Omul (Op_int)) (Pconst (6)%Z) (Pconst (8)%Z))) AT_none (aword U256) (Pvar t256_4))
    ; MkI dummy_instr_info (Cassgn (Lvar t128_0_0.(gv)) AT_none (aword U128) (Pget Aligned AAscale U256 state_3 (Pconst (2)%Z)))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U64 st_0.(gv) (Pconst (10)%Z) ] AT_none (Oasm ((BaseOp ((None), VMOVLPD)))) [:: Pvar t128_0_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3
                                                                    ; Pvar t256_1_0
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_0.(gv) (Papp2 (Omul (Op_int)) (Pconst (11)%Z) (Pconst (8)%Z))) AT_none (aword U256) (Pvar t256_4))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U64 st_0.(gv) (Pconst (15)%Z) ] AT_none (Oasm ((BaseOp ((None), VMOVHPD)))) [:: Pvar t128_1_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_0
                                                                    ; Pvar t256_0_0
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_0.(gv) (Papp2 (Omul (Op_int)) (Pconst (16)%Z) (Pconst (8)%Z))) AT_none (aword U256) (Pvar t256_4))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U64 st_0.(gv) (Pconst (20)%Z) ] AT_none (Oasm ((BaseOp ((None), VMOVHPD)))) [:: Pvar t128_0_0 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_0
                                                                    ; Pvar t256_2_0
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_0.(gv) (Papp2 (Omul (Op_int)) (Pconst (21)%Z) (Pconst (8)%Z))) AT_none (aword U256) (Pvar t256_4)) ].

Definition fd___stavx2_unpack : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___stavx2_unpack;
    f_params := args___stavx2_unpack;
    f_body := body___stavx2_unpack;
    f_tyout := tyout___stavx2_unpack;
    f_res := res___stavx2_unpack;
    f_extra := tt;
  |}.

End IDO.
