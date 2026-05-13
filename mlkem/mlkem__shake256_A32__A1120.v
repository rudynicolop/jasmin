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

(* _shake256_A32__A1120 *)
(* Local variables *)
Definition out_14277 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 14277).
Definition j_in_14278 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 14278).
Definition st_14279 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 14279).

(* Signature *)
Definition tyin__shake256_A32__A1120 : seq atype :=
  [:: aarr U8 32; aarr U8 1120 ].
Definition args__shake256_A32__A1120 : seq var_i :=
  [:: out_14277.(gv); j_in_14278.(gv) ].
Definition tyout__shake256_A32__A1120 : seq atype := [:: aarr U8 32 ].
Definition res__shake256_A32__A1120 : seq var_i := [:: out_14277.(gv) ].

(* Body *)
Definition body__shake256_A32__A1120 : cmd :=
  [:: ccall [:: Lvar st_14279.(gv) ] __state_init_avx2 [::]
    ; ccall [:: Lvar st_14279.(gv); Lnone dummy_var_info (aint) ] A1120____absorb_avx2 [:: Pvar st_14279
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar j_in_14278
                                                                    ; Pconst (31)%Z
                                                                    ; Pconst (136)%Z ]
    ; ccall [:: Lnone dummy_var_info (aarr U256 7); Lvar out_14277.(gv) ] A32____squeeze_avx2 [:: Pvar st_14279
                                                                    ; Pvar out_14277
                                                                    ; Pconst (136)%Z ] ].

Definition fd__shake256_A32__A1120 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__shake256_A32__A1120;
    f_params := args__shake256_A32__A1120;
    f_body := body__shake256_A32__A1120;
    f_tyout := tyout__shake256_A32__A1120;
    f_res := res__shake256_A32__A1120;
    f_extra := tt;
  |}.

End IDO.
