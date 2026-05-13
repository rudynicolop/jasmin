From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* __gen_matrix_sample_one_polynomial *)
(* Local variables *)
Definition pol_13744 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13744).
Definition buf_13745 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 13745).
Definition rho_13746 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13746).
Definition rc_13747 : gvar := mk_rocq_gvar Slocal (aword U16) (mkident 13747).
Definition pos_13748 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 13748).
Definition stavx2 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 13749).

(* Signature *)
Definition tyin___gen_matrix_sample_one_polynomial : seq atype :=
  [:: aarr U16 256; aarr U8 536; aarr U8 32; aword U16 ].
Definition args___gen_matrix_sample_one_polynomial : seq var_i :=
  [:: pol_13744.(gv); buf_13745.(gv); rho_13746.(gv); rc_13747.(gv) ].
Definition tyout___gen_matrix_sample_one_polynomial : seq atype :=
  [:: aarr U16 256; aarr U8 536 ].
Definition res___gen_matrix_sample_one_polynomial : seq var_i :=
  [:: pol_13744.(gv); buf_13745.(gv) ].

(* Body *)
Definition body___gen_matrix_sample_one_polynomial : cmd :=
  [:: cassgn (Laset Aligned AAscale U16 pos_13748.(gv) (Pconst (0)%Z)) (aword U16) (Pvar rc_13747)
    ; ccall [:: Lvar stavx2.(gv) ] _shake128_absorb_A32_A2 [:: Pvar rho_13746
                                                             ; Pvar pos_13748 ]
    ; ccall [:: Lvar buf_13745.(gv) ] _shake128_squeeze3blocks [:: Pvar buf_13745
                                                                 ; Pvar stavx2 ]
    ; ccall [:: Lvar pol_13744.(gv); Lvar buf_13745.(gv) ] __gen_matrix_fill_polynomial [:: Pvar pol_13744
                                                                    ; Pvar buf_13745 ] ].

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
