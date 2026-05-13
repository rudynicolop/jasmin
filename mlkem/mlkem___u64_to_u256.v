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

(* __u64_to_u256 *)
(* Local variables *)
Definition x_18863 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18863).
Definition L : gvar := mk_rocq_gvar Slocal (aint) (mkident 18864).
Definition t256 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18865).
Definition t128_18866 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18866).

(* Signature *)
Definition tyin___u64_to_u256 : seq atype := [:: aword U64; aint ].
Definition args___u64_to_u256 : seq var_i := [:: x_18863.(gv); L.(gv) ].
Definition tyout___u64_to_u256 : seq atype := [:: aword U256 ].
Definition res___u64_to_u256 : seq var_i := [:: t256.(gv) ].

(* Body *)
Definition body___u64_to_u256 : cmd :=
  [:: cif
        (Papp2 (Oeq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar L) (Pconst (2)%Z)) (Pconst (0)%Z))
        [:: cassgn (Lvar t128_18866.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar x_18863)) ]
        [:: copn [:: Lvar t128_18866.(gv) ] (Oasm ((ExtOp (Oset0 U128)))) [::]
          ; copn [:: Lvar t128_18866.(gv) ] (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_18866
                                                                    ; Pvar x_18863
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
    ; copn [:: Lvar t256.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::]
    ; cif
        (Papp2 (Oeq (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar L) (Pconst (2)%Z)) (Pconst (0)%Z))
        [:: copn [:: Lvar t256.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar t256
                                                                    ; Pvar t128_18866
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (0)%Z) ] ]
        [:: copn [:: Lvar t256.(gv) ] (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar t256
                                                                    ; Pvar t128_18866
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ] ].

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
