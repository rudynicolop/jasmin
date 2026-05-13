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

(* __gen_matrix_fill_polynomial *)
(* Local variables *)
Definition pol_13772 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13772).
Definition buf_13773 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 13773).
Definition buf_offset_13774 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13774).
Definition counter_13775 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13775).

(* Signature *)
Definition tyin___gen_matrix_fill_polynomial : seq atype :=
  [:: aarr U16 256; aarr U8 536 ].
Definition args___gen_matrix_fill_polynomial : seq var_i :=
  [:: pol_13772.(gv); buf_13773.(gv) ].
Definition tyout___gen_matrix_fill_polynomial : seq atype :=
  [:: aarr U16 256; aarr U8 536 ].
Definition res___gen_matrix_fill_polynomial : seq var_i :=
  [:: pol_13772.(gv); buf_13773.(gv) ].

(* Body *)
Definition body___gen_matrix_fill_polynomial : cmd :=
  [:: cassgn (Lvar buf_offset_13774.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
    ; cassgn (Lvar counter_13775.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
    ; ccall [:: Lvar pol_13772.(gv); Lvar counter_13775.(gv) ] _gen_matrix_buf_rejection [:: Pvar pol_13772
                                                                    ; Pvar counter_13775
                                                                    ; Pvar buf_13773
                                                                    ; Pvar buf_offset_13774 ]
    ; cassgn (Lvar buf_offset_13774.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (168)%Z)))
    ; cwhile
        [::]
        (Papp2 (Olt (Cmp_w Unsigned U64)) (Pvar counter_13775) (Papp1 (Oword_of_int U64) (Pconst (256)%Z)))
        [:: ccall [:: Lvar buf_13773.(gv) ] _shake128_next_state [:: Pvar buf_13773 ]
          ; ccall [:: Lvar pol_13772.(gv); Lvar counter_13775.(gv) ] _gen_matrix_buf_rejection [:: Pvar pol_13772
                                                                    ; Pvar counter_13775
                                                                    ; Pvar buf_13773
                                                                    ; Pvar buf_offset_13774 ] ] ].

Definition fd___gen_matrix_fill_polynomial : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___gen_matrix_fill_polynomial;
    f_params := args___gen_matrix_fill_polynomial;
    f_body := body___gen_matrix_fill_polynomial;
    f_tyout := tyout___gen_matrix_fill_polynomial;
    f_res := res___gen_matrix_fill_polynomial;
    f_extra := tt;
  |}.

End IDO.
