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

(* __addratebit_avx2 *)
(* Local variables *)
Definition st_18821 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 18821).
Definition RATE_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18822).
Definition t64_18823 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18823).
Definition R_18824 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18824).
Definition L_18825 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18825).
Definition t256_18826 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18826).

(* Signature *)
Definition tyin___addratebit_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition args___addratebit_avx2 : seq var_i :=
  [:: st_18821.(gv); RATE_8.(gv) ].
Definition tyout___addratebit_avx2 : seq atype := [:: aarr U256 7 ].
Definition res___addratebit_avx2 : seq var_i := [:: st_18821.(gv) ].

(* Body *)
Definition body___addratebit_avx2 : cmd :=
  [:: cassgn (Lvar t64_18823.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (1)%Z))
    ; cassgn (Lvar t64_18823.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar t64_18823) (Papp1 (Oword_of_int U8) (Papp2 (Omod Unsigned (Op_int)) (Papp2 (Osub (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar RATE_8)) (Pconst (1)%Z)) (Pconst (64)%Z))))
    ; ccall [:: Lvar R_18824.(gv); Lvar L_18825.(gv) ] __stavx2_pos_avx2 [:: Papp2 (Odiv Unsigned (Op_int)) (Papp2 (Osub (Op_int)) (Pvar RATE_8) (Pconst (1)%Z)) (Pconst (8)%Z) ]
    ; cif
        (Papp2 (Oeq (Op_int)) (Pvar R_18824) (Pconst (0)%Z))
        [:: copn [:: Lvar t256_18826.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t64_18823 ] ]
        [:: ccall [:: Lvar t256_18826.(gv) ] __u64_to_u256 [:: Pvar t64_18823
                                                             ; Pvar L_18825 ] ]
    ; cassgn (Laset Aligned AAscale U256 st_18821.(gv) (Pvar R_18824)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_18821 (Pvar R_18824)) (Pvar t256_18826)) ].

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
