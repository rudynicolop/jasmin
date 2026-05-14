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
Definition st0_18581 : gvar :=
  mk_rocq_gvar Slocal (aarr U64 25) (mkident 18581).
Definition st1_18582 : gvar :=
  mk_rocq_gvar Slocal (aarr U64 25) (mkident 18582).
Definition st2_18583 : gvar :=
  mk_rocq_gvar Slocal (aarr U64 25) (mkident 18583).
Definition st3_18584 : gvar :=
  mk_rocq_gvar Slocal (aarr U64 25) (mkident 18584).
Definition r8_18585 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18585).
Definition r56_18586 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18586).
Definition st4x1 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18587).
Definition st4x2 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18588).

(* Signature *)
Definition tyin___keccakf1600_pround_unpacked : seq atype :=
  [:: aarr U64 25; aarr U64 25; aarr U64 25; aarr U64 25 ].
Definition args___keccakf1600_pround_unpacked : seq var_i :=
  [:: st0_18581.(gv); st1_18582.(gv); st2_18583.(gv); st3_18584.(gv) ].
Definition tyout___keccakf1600_pround_unpacked : seq atype :=
  [:: aarr U64 25; aarr U64 25; aarr U64 25; aarr U64 25 ].
Definition res___keccakf1600_pround_unpacked : seq var_i :=
  [:: st0_18581.(gv); st1_18582.(gv); st2_18583.(gv); st3_18584.(gv) ].

(* Body *)
Definition body___keccakf1600_pround_unpacked : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar r8_18585.(gv)) AT_none (aword U256) (Pvar ROL8))
    ; MkI dummy_instr_info (Cassgn (Lvar r56_18586.(gv)) AT_none (aword U256) (Pvar ROL56))
    ; MkI dummy_instr_info (Ccall [:: Lvar st4x1.(gv) ] __st4x_pack [:: Pvar st4x1
                                                                    ; Pvar st0_18581
                                                                    ; Pvar st1_18582
                                                                    ; Pvar st2_18583
                                                                    ; Pvar st3_18584 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st4x2.(gv) ] _keccakf1600_4x_pround [:: Pvar st4x2
                                                                    ; Pvar st4x1
                                                                    ; Pvar r8_18585
                                                                    ; Pvar r56_18586 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st0_18581.(gv)
                                    ; Lvar st1_18582.(gv)
                                    ; Lvar st2_18583.(gv)
                                    ; Lvar st3_18584.(gv) ] __st4x_unpack [:: Pvar st0_18581
                                                                    ; Pvar st1_18582
                                                                    ; Pvar st2_18583
                                                                    ; Pvar st3_18584
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
