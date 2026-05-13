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

(* ABUFLEN____a_ilen_write_upto8 *)
(* Local variables *)
Definition buf_14645 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14645).
Definition offset_14646 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14646).
Definition DELTA_14647 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14647).
Definition LEN_14648 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14648).
Definition w_14649 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14649).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aword U64 ].
Definition args_ABUFLEN____a_ilen_write_upto8 : seq var_i :=
  [:: buf_14645.(gv)
    ; offset_14646.(gv)
    ; DELTA_14647.(gv)
    ; LEN_14648.(gv)
    ; w_14649.(gv) ].
Definition tyout_ABUFLEN____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 536; aint; aint ].
Definition res_ABUFLEN____a_ilen_write_upto8 : seq var_i :=
  [:: buf_14645.(gv); DELTA_14647.(gv); LEN_14648.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_write_upto8 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_14648))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_14648))
              [:: cassgn (Laset Unaligned AAdirect U64 buf_14645.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14646) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14647))))) (aword U64) (Pvar w_14649)
                ; cassgn (Lvar DELTA_14647.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14647) (Pconst (8)%Z))
                ; cassgn (Lvar LEN_14648.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14648) (Pconst (8)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_14648))
                    [:: cassgn (Laset Unaligned AAdirect U32 buf_14645.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14646) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14647))))) (aword U32) (Pvar w_14649)
                      ; cassgn (Lvar w_14649.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar w_14649) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)))
                      ; cassgn (Lvar DELTA_14647.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14647) (Pconst (4)%Z))
                      ; cassgn (Lvar LEN_14648.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14648) (Pconst (4)%Z)) ]
                    [::]
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_14648))
                    [:: cassgn (Laset Unaligned AAdirect U16 buf_14645.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14646) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14647))))) (aword U16) (Pvar w_14649)
                      ; cassgn (Lvar w_14649.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar w_14649) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))
                      ; cassgn (Lvar DELTA_14647.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14647) (Pconst (2)%Z))
                      ; cassgn (Lvar LEN_14648.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14648) (Pconst (2)%Z)) ]
                    [::]
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_14648))
                    [:: cassgn (Laset Unaligned AAdirect U8 buf_14645.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14646) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14647))))) (aword U8) (Pvar w_14649)
                      ; cassgn (Lvar DELTA_14647.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14647) (Pconst (1)%Z))
                      ; cassgn (Lvar LEN_14648.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14648) (Pconst (1)%Z)) ]
                    [::] ] ]
        [::] ].

Definition fd_ABUFLEN____a_ilen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_write_upto8;
    f_params := args_ABUFLEN____a_ilen_write_upto8;
    f_body := body_ABUFLEN____a_ilen_write_upto8;
    f_tyout := tyout_ABUFLEN____a_ilen_write_upto8;
    f_res := res_ABUFLEN____a_ilen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
