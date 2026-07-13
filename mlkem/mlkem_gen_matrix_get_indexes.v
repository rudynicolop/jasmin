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

(* gen_matrix_get_indexes *)
(* Local variables *)
Definition b_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13780).
Definition _t : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13781).
Definition t_17 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13782).
Definition idxs : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13783).

(* Signature *)
Definition tyin_gen_matrix_get_indexes : seq atype :=
  [:: aword U64; aword U64 ].
Definition args_gen_matrix_get_indexes : seq var_i := [:: b_9.(gv); _t.(gv) ].
Definition tyout_gen_matrix_get_indexes : seq atype := [:: aword U64 ].
Definition res_gen_matrix_get_indexes : seq var_i := [:: t_17.(gv) ].

(* Body *)
Definition body_gen_matrix_get_indexes : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar idxs.(gv)) AT_none (aarr U8 32) (Pvar gen_matrix_indexes))
    ; MkI dummy_instr_info (Cassgn (Lvar t_17.(gv)) AT_none (aword U64) (Pvar _t))
    ; MkI dummy_instr_info (Cassgn (Lvar t_17.(gv)) AT_none (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar t_17) (Papp1 (Oword_of_int U8) (Papp2 (Oadd (Op_int)) (Pconst (3)%Z) (Pconst (1)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar b_9.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar b_9) (Pvar t_17)))
    ; MkI dummy_instr_info (Cassgn (Lvar t_17.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 idxs (Papp1 (Oint_of_word Unsigned U64) (Pvar b_9)))) ].

Definition fd_gen_matrix_get_indexes : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_gen_matrix_get_indexes;
    f_params := args_gen_matrix_get_indexes;
    f_body := body_gen_matrix_get_indexes;
    f_tyout := tyout_gen_matrix_get_indexes;
    f_res := res_gen_matrix_get_indexes;
    f_extra := tt;
  |}.

End IDO.
