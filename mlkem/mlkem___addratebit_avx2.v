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

(* __addratebit_avx2 *)
(* Local variables *)
Definition st_3 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 18821).
Definition RATE_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18822).
Definition t64_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18823).
Definition R_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18824).
Definition L_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18825).
Definition t256_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18826).

(* Signature *)
Definition tyin___addratebit_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition args___addratebit_avx2 : seq var_i := [:: st_3.(gv); RATE_8.(gv) ].
Definition tyout___addratebit_avx2 : seq atype := [:: aarr U256 7 ].
Definition res___addratebit_avx2 : seq var_i := [:: st_3.(gv) ].

(* Body *)
Definition body___addratebit_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar t64_0.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (1)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar t64_0.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar t64_0) (Papp1 (Oword_of_int U8) (Papp2 (Omod Unsigned (Op_int)) (Papp2 (Osub (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar RATE_8)) (Pconst (1)%Z)) (Pconst (64)%Z)))))
    ; MkI dummy_instr_info (Ccall [:: Lvar R_0.(gv); Lvar L_1.(gv) ] __stavx2_pos_avx2 [:: Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Osub (Op_int)) (Pvar RATE_8) (Pconst (1)%Z)) (Pconst (8)%Z) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oeq (Op_int)) (Pvar R_0) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Copn [:: Lvar t256_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t64_0 ]) ]
                              [:: MkI dummy_instr_info (Ccall [:: Lvar t256_0.(gv) ] __u64_to_u256 [:: Pvar t64_0
                                                                    ; Pvar L_1 ]) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_3.(gv) (Pvar R_0)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_3 (Pvar R_0)) (Pvar t256_0))) ].

Definition fd___addratebit_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___addratebit_avx2;
    f_params := args___addratebit_avx2;
    f_body := body___addratebit_avx2;
    f_tyout := tyout___addratebit_avx2;
    f_res := res___addratebit_avx2;
    f_extra := tt;
  |}.

End IDO.
