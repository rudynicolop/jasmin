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

(* _shake256_A32__A1600 *)
(* Local variables *)
Definition out_5 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 14271).
Definition j_in_4 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14272).
Definition st_131 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14273).

(* Signature *)
Definition tyin__shake256_A32__A1600 : seq atype :=
  [:: aarr U8 32; aarr U8 1600 ].
Definition args__shake256_A32__A1600 : seq var_i :=
  [:: out_5.(gv); j_in_4.(gv) ].
Definition tyout__shake256_A32__A1600 : seq atype := [:: aarr U8 32 ].
Definition res__shake256_A32__A1600 : seq var_i := [:: out_5.(gv) ].

(* Body *)
Definition body__shake256_A32__A1600 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar st_131.(gv) ] __state_init_avx2 [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_131.(gv)
                                    ; Lnone dummy_var_info (aint) ] A1600____absorb_avx2 [:: Pvar st_131
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar j_in_4
                                                                    ; Pconst (31)%Z
                                                                    ; Pconst (136)%Z ])
    ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aarr U256 7)
                                    ; Lvar out_5.(gv) ] A32____squeeze_avx2 [:: Pvar st_131
                                                                    ; Pvar out_5
                                                                    ; Pconst (136)%Z ]) ].

Definition fd__shake256_A32__A1600 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__shake256_A32__A1600;
    f_params := args__shake256_A32__A1600;
    f_body := body__shake256_A32__A1600;
    f_tyout := tyout__shake256_A32__A1600;
    f_res := res__shake256_A32__A1600;
    f_extra := tt;
  |}.

End IDO.
