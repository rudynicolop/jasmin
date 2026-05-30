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

(* _shake128x4_absorb_A32_A2 *)
(* Local variables *)
Definition st_125 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14316).
Definition seed_2 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 14317).
Definition pos_0 : gvar := mk_rocq_gvar Slocal (aarr U8 8) (mkident 14318).
Definition AT_115 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14319).

(* Signature *)
Definition tyin__shake128x4_absorb_A32_A2 : seq atype :=
  [:: aarr U256 25; aarr U8 32; aarr U8 8 ].
Definition args__shake128x4_absorb_A32_A2 : seq var_i :=
  [:: st_125.(gv); seed_2.(gv); pos_0.(gv) ].
Definition tyout__shake128x4_absorb_A32_A2 : seq atype := [:: aarr U256 25 ].
Definition res__shake128x4_absorb_A32_A2 : seq var_i := [:: st_125.(gv) ].

(* Body *)
Definition body__shake128x4_absorb_A32_A2 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar st_125.(gv) ] __state_init_avx2x4 [:: Pvar st_125 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_125.(gv); Lvar AT_115.(gv) ] A32____absorb_bcast_avx2x4 [:: Pvar st_125
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar seed_2
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (168)%Z ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_125.(gv)
                                    ; Lnone dummy_var_info (aint) ] A2____absorb_avx2x4 [:: Pvar st_125
                                                                    ; Pconst (32)%Z
                                                                    ; Psub AAscale U8 2 pos_0 (Pconst (0)%Z)
                                                                    ; Psub AAscale U8 2 pos_0 (Pconst (2)%Z)
                                                                    ; Psub AAscale U8 2 pos_0 (Pconst (4)%Z)
                                                                    ; Psub AAscale U8 2 pos_0 (Pconst (6)%Z)
                                                                    ; Pconst (31)%Z
                                                                    ; Pconst (168)%Z ]) ].

Definition fd__shake128x4_absorb_A32_A2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__shake128x4_absorb_A32_A2;
    f_params := args__shake128x4_absorb_A32_A2;
    f_body := body__shake128x4_absorb_A32_A2;
    f_tyout := tyout__shake128x4_absorb_A32_A2;
    f_res := res__shake128x4_absorb_A32_A2;
    f_extra := tt;
  |}.

End IDO.
