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

(* _sha3_512A_A33 *)
(* Local variables *)
Definition out : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 14362).
Definition j_in : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 14363).
Definition st_120 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14364).

(* Signature *)
Definition tyin__sha3_512A_A33 : seq atype := [:: aarr U8 64; aarr U8 33 ].
Definition args__sha3_512A_A33 : seq var_i := [:: out.(gv); j_in.(gv) ].
Definition tyout__sha3_512A_A33 : seq atype := [:: aarr U8 64 ].
Definition res__sha3_512A_A33 : seq var_i := [:: out.(gv) ].

(* Body *)
Definition body__sha3_512A_A33 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar st_120.(gv) ] __state_init_avx2 [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_120.(gv)
                                    ; Lnone dummy_var_info (aint) ] A33____absorb_avx2 [:: Pvar st_120
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar j_in
                                                                    ; Pconst (6)%Z
                                                                    ; Pconst (72)%Z ])
    ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aarr U256 7)
                                    ; Lvar out.(gv) ] A64____squeeze_avx2 [:: Pvar st_120
                                                                    ; Pvar out
                                                                    ; Pconst (72)%Z ]) ].

Definition fd__sha3_512A_A33 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__sha3_512A_A33;
    f_params := args__sha3_512A_A33;
    f_body := body__sha3_512A_A33;
    f_tyout := tyout__sha3_512A_A33;
    f_res := res__sha3_512A_A33;
    f_extra := tt;
  |}.

End IDO.
