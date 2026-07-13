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

(* _shake128_absorb_A32_A2 *)
(* Local variables *)
Definition seed_1 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 14324).
Definition pos : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 14325).
Definition st_124 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14326).

(* Signature *)
Definition tyin__shake128_absorb_A32_A2 : seq atype :=
  [:: aarr U8 32; aarr U8 2 ].
Definition args__shake128_absorb_A32_A2 : seq var_i :=
  [:: seed_1.(gv); pos.(gv) ].
Definition tyout__shake128_absorb_A32_A2 : seq atype := [:: aarr U256 7 ].
Definition res__shake128_absorb_A32_A2 : seq var_i := [:: st_124.(gv) ].

(* Body *)
Definition body__shake128_absorb_A32_A2 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar st_124.(gv) ] __state_init_avx2 [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_124.(gv)
                                    ; Lnone dummy_var_info (aint) ] A32____absorb_avx2 [:: Pvar st_124
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar seed_1
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (168)%Z ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_124.(gv)
                                    ; Lnone dummy_var_info (aint) ] A2____absorb_avx2 [:: Pvar st_124
                                                                    ; Pconst (32)%Z
                                                                    ; Pvar pos
                                                                    ; Pconst (31)%Z
                                                                    ; Pconst (168)%Z ]) ].

Definition fd__shake128_absorb_A32_A2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__shake128_absorb_A32_A2;
    f_params := args__shake128_absorb_A32_A2;
    f_body := body__shake128_absorb_A32_A2;
    f_tyout := tyout__shake128_absorb_A32_A2;
    f_res := res__shake128_absorb_A32_A2;
    f_extra := tt;
  |}.

End IDO.
