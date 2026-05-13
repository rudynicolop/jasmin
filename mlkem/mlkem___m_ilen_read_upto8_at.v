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

(* __m_ilen_read_upto8_at *)
(* Local variables *)
Definition buf : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18968).
Definition LEN : gvar := mk_rocq_gvar Slocal (aint) (mkident 18969).
Definition TRAIL : gvar := mk_rocq_gvar Slocal (aint) (mkident 18970).
Definition CUR : gvar := mk_rocq_gvar Slocal (aint) (mkident 18971).
Definition AT : gvar := mk_rocq_gvar Slocal (aint) (mkident 18972).
Definition w : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18973).
Definition AT8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18974).
Definition t16 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18975).
Definition t8_18976 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18976).

(* Signature *)
Definition tyin___m_ilen_read_upto8_at : seq atype :=
  [:: aword U64; aint; aint; aint; aint ].
Definition args___m_ilen_read_upto8_at : seq var_i :=
  [:: buf.(gv); LEN.(gv); TRAIL.(gv); CUR.(gv); AT.(gv) ].
Definition tyout___m_ilen_read_upto8_at : seq atype :=
  [:: aword U64; aint; aint; aint; aword U64 ].
Definition res___m_ilen_read_upto8_at : seq var_i :=
  [:: buf.(gv); LEN.(gv); TRAIL.(gv); AT.(gv); w.(gv) ].

(* Body *)
Definition body___m_ilen_read_upto8_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT) (Pvar CUR)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR) (Pconst (8)%Z)) (Pvar AT))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL) (Pconst (0)%Z))))
        [:: cassgn (Lvar w.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)) ]
        [:: cassgn (Lvar AT8.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT) (Pvar CUR))
          ; cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN))
              [:: cassgn (Lvar w.(gv)) (aword U64) (Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf)))
                ; ccall [:: Lvar w.(gv) ] __SHLQ [:: Pvar w; Pvar AT8 ]
                ; cassgn (Lvar buf.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8))))
                ; cassgn (Lvar LEN.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8)))
                ; cassgn (Lvar AT8.(gv)) (aint) (Pconst (8)%Z) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN))
                    [:: cassgn (Lvar w.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pload Unaligned U32 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf))))
                      ; ccall [:: Lvar w.(gv) ] __SHLQ [:: Pvar w; Pvar AT8 ]
                      ; cassgn (Lvar buf.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8)) (Pconst (4)%Z))))
                      ; cassgn (Lvar LEN.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8)) (Pconst (4)%Z)))
                      ; cassgn (Lvar AT8.(gv)) (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8))) ]
                    [:: cassgn (Lvar w.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)) ]
                ; cif
                    (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN)))
                    [:: cassgn (Lvar t16.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pload Unaligned U16 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf))))
                      ; cassgn (Lvar buf.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8)) (Pconst (2)%Z))))
                      ; cassgn (Lvar LEN.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8)) (Pconst (2)%Z)))
                      ; ccall [:: Lvar t16.(gv) ] __SHLQ [:: Pvar t16
                                                           ; Pvar AT8 ]
                      ; cassgn (Lvar w.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w) (Pvar t16))
                      ; cassgn (Lvar AT8.(gv)) (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8))) ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pvar AT8) (Pconst (8)%Z))
                    [:: cif
                          (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN))
                          [:: cassgn (Lvar t8_18976.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pload Unaligned U8 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf))))
                            ; cassgn (Lvar t8_18976.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar t8_18976) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL) (Pconst (256)%Z)))))
                            ; cassgn (Lvar buf.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))
                            ; cassgn (Lvar LEN.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN) (Pconst (1)%Z))
                            ; ccall [:: Lvar t8_18976.(gv) ] __SHLQ [:: Pvar t8_18976
                                                                    ; Pvar AT8 ]
                            ; cassgn (Lvar w.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w) (Pvar t8_18976))
                            ; cassgn (Lvar AT8.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8) (Pconst (1)%Z))
                            ; cif
                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                [:: cassgn (Lvar AT8.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8) (Pconst (1)%Z))
                                  ; cassgn (Lvar TRAIL.(gv)) (aint) (Pconst (0)%Z) ]
                                [::] ]
                          [:: cif
                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL) (Pconst (256)%Z)) (Pconst (0)%Z))
                                [:: cassgn (Lvar t8_18976.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL) (Pconst (256)%Z)))
                                  ; ccall [:: Lvar t8_18976.(gv) ] __SHLQ [:: Pvar t8_18976
                                                                    ; Pvar AT8 ]
                                  ; cassgn (Lvar w.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w) (Pvar t8_18976))
                                  ; cassgn (Lvar TRAIL.(gv)) (aint) (Pconst (0)%Z)
                                  ; cassgn (Lvar AT8.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8) (Pconst (1)%Z)) ]
                                [::] ] ]
                    [::] ]
          ; cassgn (Lvar AT.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR) (Pvar AT8)) ] ].

Definition fd___m_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___m_ilen_read_upto8_at;
    f_params := args___m_ilen_read_upto8_at;
    f_body := body___m_ilen_read_upto8_at;
    f_tyout := tyout___m_ilen_read_upto8_at;
    f_res := res___m_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
