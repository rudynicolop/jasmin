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

(* __keccakf1600_avx2 *)
(* Local variables *)
Definition state_19016 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 19016).
Definition round_constants : gvar :=
  mk_rocq_gvar Slocal (aarr U64 24) (mkident 19017).
Definition r_19018 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 19018).
Definition rc : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19019).

(* Signature *)
Definition tyin___keccakf1600_avx2 : seq atype := [:: aarr U256 7 ].
Definition args___keccakf1600_avx2 : seq var_i := [:: state_19016.(gv) ].
Definition tyout___keccakf1600_avx2 : seq atype := [:: aarr U256 7 ].
Definition res___keccakf1600_avx2 : seq var_i := [:: state_19016.(gv) ].

(* Body *)
Definition body___keccakf1600_avx2 : cmd :=
  [:: cassgn (Lvar round_constants.(gv)) (aarr U64 24) (Pvar KECCAK1600_RC)
    ; cassgn (Lvar r_19018.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [:: ccall [:: Lvar state_19016.(gv) ] __keccakf1600_pround_avx2 [:: Pvar state_19016 ]
          ; copn [:: Lvar rc.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Aligned AAscale U64 round_constants (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar r_19018)) ]
          ; cassgn (Laset Aligned AAscale U256 state_19016.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 state_19016 (Pconst (0)%Z)) (Pvar rc))
          ; cassgn (Lvar r_19018.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar r_19018) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar r_19018) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (24)%Z)))
        [::] ].

Definition fd___keccakf1600_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___keccakf1600_avx2;
    f_params := args___keccakf1600_avx2;
    f_body := body___keccakf1600_avx2;
    f_tyout := tyout___keccakf1600_avx2;
    f_res := res___keccakf1600_avx2;
    f_extra := tt;
  |}.

End IDO.
