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

(* _sha3_256A_A1568 *)
(* Local variables *)
Definition out_3 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 14283).
Definition j_in_2 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 14284).
Definition st_129 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14285).

(* Signature *)
Definition tyin__sha3_256A_A1568 : seq atype :=
  [:: aarr U8 32; aarr U8 1568 ].
Definition args__sha3_256A_A1568 : seq var_i := [:: out_3.(gv); j_in_2.(gv) ].
Definition tyout__sha3_256A_A1568 : seq atype := [:: aarr U8 32 ].
Definition res__sha3_256A_A1568 : seq var_i := [:: out_3.(gv) ].

(* Body *)
Definition body__sha3_256A_A1568 : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar st_129.(gv) ] __state_init_avx2 [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_129.(gv)
                                    ; Lnone dummy_var_info (aint) ] A1568____absorb_avx2 [:: Pvar st_129
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar j_in_2
                                                                    ; Pconst (6)%Z
                                                                    ; Pconst (136)%Z ])
    ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aarr U256 7)
                                    ; Lvar out_3.(gv) ] A32____squeeze_avx2 [:: Pvar st_129
                                                                    ; Pvar out_3
                                                                    ; Pconst (136)%Z ]) ].

Definition fd__sha3_256A_A1568 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__sha3_256A_A1568;
    f_params := args__sha3_256A_A1568;
    f_body := body__sha3_256A_A1568;
    f_tyout := tyout__sha3_256A_A1568;
    f_res := res__sha3_256A_A1568;
    f_extra := tt;
  |}.

End IDO.
