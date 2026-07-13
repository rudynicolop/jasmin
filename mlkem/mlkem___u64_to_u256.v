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

(* __u64_to_u256 *)
(* Local variables *)
Definition x_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18863).
Definition L : gvar := mk_rocq_gvar Slocal (aint) (mkident 18864).
Definition t256 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18865).
Definition t128_1 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18866).

(* Signature *)
Definition tyin___u64_to_u256 : seq atype := [:: aword U64; aint ].
Definition args___u64_to_u256 : seq var_i := [:: x_8.(gv); L.(gv) ].
Definition tyout___u64_to_u256 : seq atype := [:: aword U256 ].
Definition res___u64_to_u256 : seq var_i := [:: t256.(gv) ].

(* Body *)
Definition body___u64_to_u256 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oeq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar L) (Pconst (2)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t128_1.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar x_8))) ]
                              [:: MkI dummy_instr_info (Copn [:: Lvar t128_1.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1
                                                                    ; Pvar x_8
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ])
    ; MkI dummy_instr_info (Copn [:: Lvar t256.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oeq (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar L) (Pconst (2)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Copn [:: Lvar t256.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar t256
                                                                    ; Pvar t128_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (0)%Z) ]) ]
                              [:: MkI dummy_instr_info (Copn [:: Lvar t256.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar t256
                                                                    ; Pvar t128_1
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ].

Definition fd___u64_to_u256 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___u64_to_u256;
    f_params := args___u64_to_u256;
    f_body := body___u64_to_u256;
    f_tyout := tyout___u64_to_u256;
    f_res := res___u64_to_u256;
    f_extra := tt;
  |}.

End IDO.
