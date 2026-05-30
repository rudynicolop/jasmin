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

(* A1568____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_110 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15873).
Definition offset_112 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15874).
Definition DELTA_74 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15875).
Definition LEN_55 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15876).
Definition TRAIL_31 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15877).
Definition CUR_31 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15878).
Definition AT_75 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15879).
Definition w_77 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15880).
Definition AT8_29 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15881).
Definition t16_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15882).
Definition t8_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15883).

(* Signature *)
Definition tyin_A1568____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1568____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_110.(gv)
    ; offset_112.(gv)
    ; DELTA_74.(gv)
    ; LEN_55.(gv)
    ; TRAIL_31.(gv)
    ; CUR_31.(gv)
    ; AT_75.(gv) ].
Definition tyout_A1568____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A1568____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_74.(gv); LEN_55.(gv); TRAIL_31.(gv); AT_75.(gv); w_77.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_75) (Pvar CUR_31)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_31) (Pconst (8)%Z)) (Pvar AT_75))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_55) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_31) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_77.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_29.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_75) (Pvar CUR_31)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_55))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_77.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_110 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_112) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_74))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_77.(gv) ] __SHLQ [:: Pvar w_77
                                                                    ; Pvar AT8_29 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_74.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_74) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_29))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_55.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_55) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_29))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_29.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_55))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_77.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_110 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_112) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_74)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_77.(gv) ] __SHLQ [:: Pvar w_77
                                                                    ; Pvar AT8_29 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_74.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_74) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_29)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_29)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_55.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_55) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_29)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_29)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_29.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_29)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_29)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_77.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_29) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_55)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_7.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_110 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_112) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_74)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_74.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_74) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_29)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_29)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_55.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_55) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_29)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_29)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_7.(gv) ] __SHLQ [:: Pvar t16_7
                                                                    ; Pvar AT8_29 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_77.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_77) (Pvar t16_7)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_29.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_29)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_29)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_29) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_55))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_8.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_110 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_112) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_74)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_8.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_8) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_31) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_74.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_74) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_55.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_55) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_8.(gv) ] __SHLQ [:: Pvar t8_8
                                                                    ; Pvar AT8_29 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_77.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_77) (Pvar t8_8)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_29.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_29) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_29) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_31) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_29.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_29) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_31.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_31) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_8.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_31) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_8.(gv) ] __SHLQ [:: Pvar t8_8
                                                                    ; Pvar AT8_29 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_77.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_77) (Pvar t8_8)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_31.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_29.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_29) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_75.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_31) (Pvar AT8_29))) ]) ].

Definition fd_A1568____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_ilen_read_upto8_at;
    f_params := args_A1568____a_ilen_read_upto8_at;
    f_body := body_A1568____a_ilen_read_upto8_at;
    f_tyout := tyout_A1568____a_ilen_read_upto8_at;
    f_res := res_A1568____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
