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

(* __gen_matrix_sample_one_polynomial *)
(* Local variables *)
Definition pol_5 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13744).
Definition buf_177 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 13745).
Definition rho_0 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13746).
Definition rc_1 : gvar := mk_rocq_gvar Slocal (aword U16) (mkident 13747).
Definition pos_1 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 13748).
Definition stavx2 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 13749).

(* Signature *)
Definition tyin___gen_matrix_sample_one_polynomial : seq atype :=
  [:: aarr U16 256; aarr U8 536; aarr U8 32; aword U16 ].
Definition args___gen_matrix_sample_one_polynomial : seq var_i :=
  [:: pol_5.(gv); buf_177.(gv); rho_0.(gv); rc_1.(gv) ].
Definition tyout___gen_matrix_sample_one_polynomial : seq atype :=
  [:: aarr U16 256; aarr U8 536 ].
Definition res___gen_matrix_sample_one_polynomial : seq var_i :=
  [:: pol_5.(gv); buf_177.(gv) ].

(* Body *)
Definition body___gen_matrix_sample_one_polynomial : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U16 pos_1.(gv) (Pconst (0)%Z)) AT_none (aword U16) (Pvar rc_1))
    ; MkI dummy_instr_info (Ccall [:: Lvar stavx2.(gv) ] _shake128_absorb_A32_A2 [:: Pvar rho_0
                                                                    ; Pvar pos_1 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_177.(gv) ] _shake128_squeeze3blocks [:: Pvar buf_177
                                                                    ; Pvar stavx2 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar pol_5.(gv); Lvar buf_177.(gv) ] __gen_matrix_fill_polynomial [:: Pvar pol_5
                                                                    ; Pvar buf_177 ]) ].

Definition fd___gen_matrix_sample_one_polynomial : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___gen_matrix_sample_one_polynomial;
    f_params := args___gen_matrix_sample_one_polynomial;
    f_body := body___gen_matrix_sample_one_polynomial;
    f_tyout := tyout___gen_matrix_sample_one_polynomial;
    f_res := res___gen_matrix_sample_one_polynomial;
    f_extra := tt;
  |}.

End IDO.
