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

(* _shake256x4_A128__A32_A1 *)
(* Local variables *)
Definition out0 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14330).
Definition out1 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14331).
Definition out2 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14332).
Definition out3 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 14333).
Definition seed_0 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 14334).
Definition nonces : gvar := mk_rocq_gvar Slocal (aarr U8 4) (mkident 14335).
Definition st_s : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 14336).
Definition st_123 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14337).

(* Signature *)
Definition tyin__shake256x4_A128__A32_A1 : seq atype :=
  [:: aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 32
    ; aarr U8 4 ].
Definition args__shake256x4_A128__A32_A1 : seq var_i :=
  [:: out0.(gv); out1.(gv); out2.(gv); out3.(gv); seed_0.(gv); nonces.(gv) ].
Definition tyout__shake256x4_A128__A32_A1 : seq atype :=
  [:: aarr U8 128; aarr U8 128; aarr U8 128; aarr U8 128 ].
Definition res__shake256x4_A128__A32_A1 : seq var_i :=
  [:: out0.(gv); out1.(gv); out2.(gv); out3.(gv) ].

(* Body *)
Definition body__shake256x4_A128__A32_A1 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar st_123.(gv)) AT_none (aarr U256 25) (Pvar st_s))
    ; MkI dummy_instr_info (Ccall [:: Lvar st_123.(gv) ] __state_init_avx2x4 [:: Pvar st_123 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_123.(gv)
                                    ; Lnone dummy_var_info (aint) ] A32____absorb_bcast_avx2x4 [:: Pvar st_123
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar seed_0
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (136)%Z ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_123.(gv)
                                    ; Lnone dummy_var_info (aint) ] A1____absorb_avx2x4 [:: Pvar st_123
                                                                    ; Pconst (32)%Z
                                                                    ; Psub AAscale U8 1 nonces (Pconst (0)%Z)
                                                                    ; Psub AAscale U8 1 nonces (Pconst (1)%Z)
                                                                    ; Psub AAscale U8 1 nonces (Pconst (2)%Z)
                                                                    ; Psub AAscale U8 1 nonces (Pconst (3)%Z)
                                                                    ; Pconst (31)%Z
                                                                    ; Pconst (136)%Z ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_123.(gv)
                                    ; Lvar out0.(gv)
                                    ; Lvar out1.(gv)
                                    ; Lvar out2.(gv)
                                    ; Lvar out3.(gv) ] A128____squeeze_avx2x4 [:: Pvar st_123
                                                                    ; Pvar out0
                                                                    ; Pvar out1
                                                                    ; Pvar out2
                                                                    ; Pvar out3
                                                                    ; Pconst (136)%Z ]) ].

Definition fd__shake256x4_A128__A32_A1 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__shake256x4_A128__A32_A1;
    f_params := args__shake256x4_A128__A32_A1;
    f_body := body__shake256x4_A128__A32_A1;
    f_tyout := tyout__shake256x4_A128__A32_A1;
    f_res := res__shake256x4_A128__A32_A1;
    f_extra := tt;
  |}.

End IDO.
