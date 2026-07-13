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

(* _sha3_256A_A1184 *)
(* Local variables *)
Definition out_2 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 14289).
Definition j_in_1 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 14290).
Definition st_128 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14291).

(* Signature *)
Definition tyin__sha3_256A_A1184 : seq atype :=
  [:: aarr U8 32; aarr U8 1184 ].
Definition args__sha3_256A_A1184 : seq var_i := [:: out_2.(gv); j_in_1.(gv) ].
Definition tyout__sha3_256A_A1184 : seq atype := [:: aarr U8 32 ].
Definition res__sha3_256A_A1184 : seq var_i := [:: out_2.(gv) ].

(* Body *)
Definition body__sha3_256A_A1184 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar st_128.(gv) ] __state_init_avx2 [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_128.(gv)
                                    ; Lnone dummy_var_info (aint) ] A1184____absorb_avx2 [:: Pvar st_128
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar j_in_1
                                                                    ; Pconst (6)%Z
                                                                    ; Pconst (136)%Z ])
    ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aarr U256 7)
                                    ; Lvar out_2.(gv) ] A32____squeeze_avx2 [:: Pvar st_128
                                                                    ; Pvar out_2
                                                                    ; Pconst (136)%Z ]) ].

Definition fd__sha3_256A_A1184 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__sha3_256A_A1184;
    f_params := args__sha3_256A_A1184;
    f_body := body__sha3_256A_A1184;
    f_tyout := tyout__sha3_256A_A1184;
    f_res := res__sha3_256A_A1184;
    f_extra := tt;
  |}.

End IDO.
