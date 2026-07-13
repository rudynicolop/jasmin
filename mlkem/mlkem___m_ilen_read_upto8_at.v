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
Definition t8_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18976).

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
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT) (Pvar CUR)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR) (Pconst (8)%Z)) (Pvar AT))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT) (Pvar CUR)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w.(gv)) AT_none (aword U64) (Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w.(gv) ] __SHLQ [:: Pvar w
                                                                    ; Pvar AT8 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8)))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pload Unaligned U32 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf)))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w.(gv) ] __SHLQ [:: Pvar w
                                                                    ; Pvar AT8 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar buf.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8)) (Pconst (4)%Z)))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pload Unaligned U16 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf)))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar buf.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8)) (Pconst (2)%Z)))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16.(gv) ] __SHLQ [:: Pvar t16
                                                                    ; Pvar AT8 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w) (Pvar t16)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_0.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pload Unaligned U8 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf)))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_0.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_0) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar buf.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_0.(gv) ] __SHLQ [:: Pvar t8_0
                                                                    ; Pvar AT8 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w) (Pvar t8_0)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_0.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_0.(gv) ] __SHLQ [:: Pvar t8_0
                                                                    ; Pvar AT8 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w) (Pvar t8_0)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR) (Pvar AT8))) ]) ].

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
