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

(* _shake128_next_state *)
(* Local variables *)
Definition buf_167 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14306).
Definition pst : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 14307).

(* Signature *)
Definition tyin__shake128_next_state : seq atype := [:: aarr U8 536 ].
Definition args__shake128_next_state : seq var_i := [:: buf_167.(gv) ].
Definition tyout__shake128_next_state : seq atype := [:: aarr U8 536 ].
Definition res__shake128_next_state : seq var_i := [:: buf_167.(gv) ].

(* Body *)
Definition body__shake128_next_state : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar pst.(gv)) AT_none (aarr U64 25) (Psub AAscale U64 25 buf_167 (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pconst (168)%Z) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Ccall [:: Lvar pst.(gv) ] _keccakf1600_st25_avx2 [:: Pvar pst ])
    ; MkI dummy_instr_info (Cassgn (Lasub AAscale U64 25 buf_167.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pconst (168)%Z) (Pconst (8)%Z)))) AT_none (aarr U64 25) (Pvar pst)) ].

Definition fd__shake128_next_state : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__shake128_next_state;
    f_params := args__shake128_next_state;
    f_body := body__shake128_next_state;
    f_tyout := tyout__shake128_next_state;
    f_res := res__shake128_next_state;
    f_extra := tt;
  |}.

End IDO.
