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

(* __keccakf1600_pround_equiv *)
(* Local variables *)
Definition e_1 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18572).
Definition a_8 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18573).
Definition st0_2 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18574).
Definition st1_2 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18575).
Definition st2_2 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18576).
Definition st3_4 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18577).

(* Signature *)
Definition tyin___keccakf1600_pround_equiv : seq atype :=
  [:: aarr U256 25; aarr U256 25 ].
Definition args___keccakf1600_pround_equiv : seq var_i :=
  [:: e_1.(gv); a_8.(gv) ].
Definition tyout___keccakf1600_pround_equiv : seq atype := [:: aarr U256 25 ].
Definition res___keccakf1600_pround_equiv : seq var_i := [:: e_1.(gv) ].

(* Body *)
Definition body___keccakf1600_pround_equiv : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar st0_2.(gv)
                                    ; Lvar st1_2.(gv)
                                    ; Lvar st2_2.(gv)
                                    ; Lvar st3_4.(gv) ] __st4x_unpack [:: Pvar st0_2
                                                                    ; Pvar st1_2
                                                                    ; Pvar st2_2
                                                                    ; Pvar st3_4
                                                                    ; Pvar a_8 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st0_2.(gv)
                                    ; Lvar st1_2.(gv)
                                    ; Lvar st2_2.(gv)
                                    ; Lvar st3_4.(gv) ] __keccakf1600_pround_unpacked [:: Pvar st0_2
                                                                    ; Pvar st1_2
                                                                    ; Pvar st2_2
                                                                    ; Pvar st3_4 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar e_1.(gv) ] __st4x_pack [:: Pvar e_1
                                                                    ; Pvar st0_2
                                                                    ; Pvar st1_2
                                                                    ; Pvar st2_2
                                                                    ; Pvar st3_4 ]) ].

Definition fd___keccakf1600_pround_equiv : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___keccakf1600_pround_equiv;
    f_params := args___keccakf1600_pround_equiv;
    f_body := body___keccakf1600_pround_equiv;
    f_tyout := tyout___keccakf1600_pround_equiv;
    f_res := res___keccakf1600_pround_equiv;
    f_extra := tt;
  |}.

End IDO.
