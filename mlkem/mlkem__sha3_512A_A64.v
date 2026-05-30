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

(* _sha3_512A_A64 *)
(* Local variables *)
Definition out_0 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 14356).
Definition j_in_0 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 14357).
Definition st_121 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14358).

(* Signature *)
Definition tyin__sha3_512A_A64 : seq atype := [:: aarr U8 64; aarr U8 64 ].
Definition args__sha3_512A_A64 : seq var_i := [:: out_0.(gv); j_in_0.(gv) ].
Definition tyout__sha3_512A_A64 : seq atype := [:: aarr U8 64 ].
Definition res__sha3_512A_A64 : seq var_i := [:: out_0.(gv) ].

(* Body *)
Definition body__sha3_512A_A64 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar st_121.(gv) ] __state_init_avx2 [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_121.(gv)
                                    ; Lnone dummy_var_info (aint) ] A64____absorb_avx2 [:: Pvar st_121
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar j_in_0
                                                                    ; Pconst (6)%Z
                                                                    ; Pconst (72)%Z ])
    ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aarr U256 7)
                                    ; Lvar out_0.(gv) ] A64____squeeze_avx2 [:: Pvar st_121
                                                                    ; Pvar out_0
                                                                    ; Pconst (72)%Z ]) ].

Definition fd__sha3_512A_A64 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__sha3_512A_A64;
    f_params := args__sha3_512A_A64;
    f_body := body__sha3_512A_A64;
    f_tyout := tyout__sha3_512A_A64;
    f_res := res__sha3_512A_A64;
    f_extra := tt;
  |}.

End IDO.
