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

(* __shuffle1 *)
(* Local variables *)
Definition a_19083 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19083).
Definition b_19084 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19084).
Definition r0_19085 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19085).
Definition r1_19086 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19086).
Definition t0_19087 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19087).
Definition t1_19088 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19088).

(* Signature *)
Definition tyin___shuffle1 : seq atype := [:: aword U256; aword U256 ].
Definition args___shuffle1 : seq var_i := [:: a_19083.(gv); b_19084.(gv) ].
Definition tyout___shuffle1 : seq atype := [:: aword U256; aword U256 ].
Definition res___shuffle1 : seq var_i := [:: r0_19085.(gv); r1_19086.(gv) ].

(* Body *)
Definition body___shuffle1 : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar t0_19087.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE32 U256))))) [:: Pvar b_19084
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (16)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar r0_19085.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE16 U256))))) [:: Pvar a_19083
                                                                    ; Pvar t0_19087
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar t1_19088.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE32 U256))))) [:: Pvar a_19083
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (16)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Lvar r1_19086.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBLEND VE16 U256))))) [:: Pvar t1_19088
                                                                    ; Pvar b_19084
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (170)%Z) ]) ].

Definition fd___shuffle1 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___shuffle1;
    f_params := args___shuffle1;
    f_body := body___shuffle1;
    f_tyout := tyout___shuffle1;
    f_res := res___shuffle1;
    f_extra := tt;
  |}.

End IDO.
