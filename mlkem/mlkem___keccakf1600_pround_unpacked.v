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

(* __keccakf1600_pround_unpacked *)
(* Local variables *)
Definition st0_1 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18581).
Definition st1_1 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18582).
Definition st2_1 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18583).
Definition st3_3 : gvar := mk_rocq_gvar Slocal (aarr U64 25) (mkident 18584).
Definition r8_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18585).
Definition r56_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18586).
Definition st4x1 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18587).
Definition st4x2 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18588).

(* Signature *)
Definition tyin___keccakf1600_pround_unpacked : seq atype :=
  [:: aarr U64 25; aarr U64 25; aarr U64 25; aarr U64 25 ].
Definition args___keccakf1600_pround_unpacked : seq var_i :=
  [:: st0_1.(gv); st1_1.(gv); st2_1.(gv); st3_3.(gv) ].
Definition tyout___keccakf1600_pround_unpacked : seq atype :=
  [:: aarr U64 25; aarr U64 25; aarr U64 25; aarr U64 25 ].
Definition res___keccakf1600_pround_unpacked : seq var_i :=
  [:: st0_1.(gv); st1_1.(gv); st2_1.(gv); st3_3.(gv) ].

(* Body *)
Definition body___keccakf1600_pround_unpacked : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar r8_1.(gv)) AT_none (aword U256) (Pvar ROL8))
    ; MkI dummy_instr_info (Cassgn (Lvar r56_1.(gv)) AT_none (aword U256) (Pvar ROL56))
    ; MkI dummy_instr_info (Ccall [:: Lvar st4x1.(gv) ] __st4x_pack [:: Pvar st4x1
                                                                    ; Pvar st0_1
                                                                    ; Pvar st1_1
                                                                    ; Pvar st2_1
                                                                    ; Pvar st3_3 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st4x2.(gv) ] _keccakf1600_4x_pround [:: Pvar st4x2
                                                                    ; Pvar st4x1
                                                                    ; Pvar r8_1
                                                                    ; Pvar r56_1 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st0_1.(gv)
                                    ; Lvar st1_1.(gv)
                                    ; Lvar st2_1.(gv)
                                    ; Lvar st3_3.(gv) ] __st4x_unpack [:: Pvar st0_1
                                                                    ; Pvar st1_1
                                                                    ; Pvar st2_1
                                                                    ; Pvar st3_3
                                                                    ; Pvar st4x2 ]) ].

Definition fd___keccakf1600_pround_unpacked : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___keccakf1600_pround_unpacked;
    f_params := args___keccakf1600_pround_unpacked;
    f_body := body___keccakf1600_pround_unpacked;
    f_tyout := tyout___keccakf1600_pround_unpacked;
    f_res := res___keccakf1600_pround_unpacked;
    f_extra := tt;
  |}.

End IDO.
