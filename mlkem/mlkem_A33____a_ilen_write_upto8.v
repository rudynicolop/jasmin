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

(* A33____a_ilen_write_upto8 *)
(* Local variables *)
Definition buf_17184 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17184).
Definition offset_17185 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17185).
Definition DELTA_17186 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17186).
Definition LEN_17187 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17187).
Definition w_17188 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17188).

(* Signature *)
Definition tyin_A33____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aword U64 ].
Definition args_A33____a_ilen_write_upto8 : seq var_i :=
  [:: buf_17184.(gv)
    ; offset_17185.(gv)
    ; DELTA_17186.(gv)
    ; LEN_17187.(gv)
    ; w_17188.(gv) ].
Definition tyout_A33____a_ilen_write_upto8 : seq atype :=
  [:: aarr U8 33; aint; aint ].
Definition res_A33____a_ilen_write_upto8 : seq var_i :=
  [:: buf_17184.(gv); DELTA_17186.(gv); LEN_17187.(gv) ].

(* Body *)
Definition body_A33____a_ilen_write_upto8 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_17187))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_17187))
              [:: cassgn (Laset Unaligned AAdirect U64 buf_17184.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17185) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17186))))) (aword U64) (Pvar w_17188)
                ; cassgn (Lvar DELTA_17186.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17186) (Pconst (8)%Z))
                ; cassgn (Lvar LEN_17187.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17187) (Pconst (8)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_17187))
                    [:: cassgn (Laset Unaligned AAdirect U32 buf_17184.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17185) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17186))))) (aword U32) (Pvar w_17188)
                      ; cassgn (Lvar w_17188.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar w_17188) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)))
                      ; cassgn (Lvar DELTA_17186.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17186) (Pconst (4)%Z))
                      ; cassgn (Lvar LEN_17187.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17187) (Pconst (4)%Z)) ]
                    [::]
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_17187))
                    [:: cassgn (Laset Unaligned AAdirect U16 buf_17184.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17185) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17186))))) (aword U16) (Pvar w_17188)
                      ; cassgn (Lvar w_17188.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar w_17188) (Papp1 (Oword_of_int U8) (Pconst (16)%Z)))
                      ; cassgn (Lvar DELTA_17186.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17186) (Pconst (2)%Z))
                      ; cassgn (Lvar LEN_17187.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17187) (Pconst (2)%Z)) ]
                    [::]
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_17187))
                    [:: cassgn (Laset Unaligned AAdirect U8 buf_17184.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17185) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17186))))) (aword U8) (Pvar w_17188)
                      ; cassgn (Lvar DELTA_17186.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17186) (Pconst (1)%Z))
                      ; cassgn (Lvar LEN_17187.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17187) (Pconst (1)%Z)) ]
                    [::] ] ]
        [::] ].

Definition fd_A33____a_ilen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_ilen_write_upto8;
    f_params := args_A33____a_ilen_write_upto8;
    f_body := body_A33____a_ilen_write_upto8;
    f_tyout := tyout_A33____a_ilen_write_upto8;
    f_res := res_A33____a_ilen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
