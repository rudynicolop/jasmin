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

(* _shake256_A128__A32_A1 *)
(* Local variables *)
Definition out_1 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14348).
Definition seed : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 14349).
Definition nonce : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 14350).
Definition st_122 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14351).

(* Signature *)
Definition tyin__shake256_A128__A32_A1 : seq atype :=
  [:: aarr U8 128; aarr U8 32; aarr U8 1 ].
Definition args__shake256_A128__A32_A1 : seq var_i :=
  [:: out_1.(gv); seed.(gv); nonce.(gv) ].
Definition tyout__shake256_A128__A32_A1 : seq atype := [:: aarr U8 128 ].
Definition res__shake256_A128__A32_A1 : seq var_i := [:: out_1.(gv) ].

(* Body *)
Definition body__shake256_A128__A32_A1 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar st_122.(gv) ] __state_init_avx2 [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_122.(gv)
                                    ; Lnone dummy_var_info (aint) ] A32____absorb_avx2 [:: Pvar st_122
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar seed
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (136)%Z ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_122.(gv)
                                    ; Lnone dummy_var_info (aint) ] A1____absorb_avx2 [:: Pvar st_122
                                                                    ; Pconst (32)%Z
                                                                    ; Pvar nonce
                                                                    ; Pconst (31)%Z
                                                                    ; Pconst (136)%Z ])
    ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aarr U256 7)
                                    ; Lvar out_1.(gv) ] A128____squeeze_avx2 [:: Pvar st_122
                                                                    ; Pvar out_1
                                                                    ; Pconst (136)%Z ]) ].

Definition fd__shake256_A128__A32_A1 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__shake256_A128__A32_A1;
    f_params := args__shake256_A128__A32_A1;
    f_body := body__shake256_A128__A32_A1;
    f_tyout := tyout__shake256_A128__A32_A1;
    f_res := res__shake256_A128__A32_A1;
    f_extra := tt;
  |}.

End IDO.
