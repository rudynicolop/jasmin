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

(* A1____a_ilen_write_upto8 *)
(* Local variables *)
Definition buf_18330 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18330).
Definition offset_18331 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18331).
Definition DELTA_18332 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18332).
Definition LEN_18333 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18333).
Definition w_18334 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18334).

(* Signature *)
Definition tyin_A1____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aword U64 ].
Definition args_A1____a_ilen_write_upto8 : seq var_i :=
  [:: buf_18330.(gv)
    ; offset_18331.(gv)
    ; DELTA_18332.(gv)
    ; LEN_18333.(gv)
    ; w_18334.(gv) ].
Definition tyout_A1____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 1; aint; aint ].
Definition res_A1____a_ilen_write_upto8 : seq var_i :=
  [:: buf_18330.(gv); DELTA_18332.(gv); LEN_18333.(gv) ].

(* Body *)
Definition body_A1____a_ilen_write_upto8 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_18333))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_18333))
              [:: cassgn (Laset Unaligned AAdirect U64 buf_18330.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18331) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18332))))) (aword U64) (Pvar w_18334)
                ; cassgn (Lvar DELTA_18332.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18332) (Pconst (8)%Z))
                ; cassgn (Lvar LEN_18333.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18333) (Pconst (8)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_18333))
                    [:: cassgn (Laset Unaligned AAdirect U32 buf_18330.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18331) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18332))))) (aword U32) (Pvar w_18334)
                      ; cassgn (Lvar w_18334.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar w_18334) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)))
                      ; cassgn (Lvar DELTA_18332.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18332) (Pconst (4)%Z))
                      ; cassgn (Lvar LEN_18333.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18333) (Pconst (4)%Z)) ]
                    [::]
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_18333))
                    [:: cassgn (Laset Unaligned AAdirect U16 buf_18330.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18331) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18332))))) (aword U16) (Pvar w_18334)
                      ; cassgn (Lvar w_18334.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar w_18334) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))
                      ; cassgn (Lvar DELTA_18332.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18332) (Pconst (2)%Z))
                      ; cassgn (Lvar LEN_18333.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18333) (Pconst (2)%Z)) ]
                    [::]
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_18333))
                    [:: cassgn (Laset Unaligned AAdirect U8 buf_18330.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18331) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18332))))) (aword U8) (Pvar w_18334)
                      ; cassgn (Lvar DELTA_18332.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18332) (Pconst (1)%Z))
                      ; cassgn (Lvar LEN_18333.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18333) (Pconst (1)%Z)) ]
                    [::] ] ]
        [::] ].

Definition fd_A1____a_ilen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_ilen_write_upto8;
    f_params := args_A1____a_ilen_write_upto8;
    f_body := body_A1____a_ilen_write_upto8;
    f_tyout := tyout_A1____a_ilen_write_upto8;
    f_res := res_A1____a_ilen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
