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

(* A1____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_18412 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18412).
Definition offset : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18413).
Definition DELTA : gvar := mk_rocq_gvar Slocal (aint) (mkident 18414).
Definition LEN_18415 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18415).
Definition TRAIL_18416 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18416).
Definition CUR_18417 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18417).
Definition AT_18418 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18418).
Definition w_18419 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18419).
Definition AT8_18420 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18420).
Definition t16_18421 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18421).
Definition t8_18422 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18422).

(* Signature *)
Definition tyin_A1____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_18412.(gv)
    ; offset.(gv)
    ; DELTA.(gv)
    ; LEN_18415.(gv)
    ; TRAIL_18416.(gv)
    ; CUR_18417.(gv)
    ; AT_18418.(gv) ].
Definition tyout_A1____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A1____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA.(gv)
    ; LEN_18415.(gv)
    ; TRAIL_18416.(gv)
    ; AT_18418.(gv)
    ; w_18419.(gv) ].

(* Body *)
Definition body_A1____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_18418) (Pvar CUR_18417)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_18417) (Pconst (8)%Z)) (Pvar AT_18418))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_18415) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_18416) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_18419.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_18420.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_18418) (Pvar CUR_18417)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_18415))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_18419.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_18412 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_18419.(gv) ] __SHLQ [:: Pvar w_18419
                                                                    ; Pvar AT8_18420 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18420))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_18415.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18415) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18420))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_18420.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_18415))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_18419.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_18412 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_18419.(gv) ] __SHLQ [:: Pvar w_18419
                                                                    ; Pvar AT8_18420 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_18420)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18420)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_18415.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18415) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_18420)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18420)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_18420.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_18420)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_18420)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_18419.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_18420) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_18415)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_18421.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_18412 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_18420)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18420)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_18415.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18415) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_18420)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18420)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_18421.(gv) ] __SHLQ [:: Pvar t16_18421
                                                                    ; Pvar AT8_18420 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_18419.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_18419) (Pvar t16_18421)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_18420.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_18420)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_18420)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_18420) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_18415))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_18422.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_18412 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_18422.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_18422) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_18416) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_18415.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18415) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_18422.(gv) ] __SHLQ [:: Pvar t8_18422
                                                                    ; Pvar AT8_18420 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_18419.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_18419) (Pvar t8_18422)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_18420.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_18420) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_18420) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_18416) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_18420.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_18420) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_18416.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_18416) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_18422.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_18416) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_18422.(gv) ] __SHLQ [:: Pvar t8_18422
                                                                    ; Pvar AT8_18420 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_18419.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_18419) (Pvar t8_18422)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_18416.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_18420.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_18420) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_18418.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_18417) (Pvar AT8_18420))) ]) ].

Definition fd_A1____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_ilen_read_upto8_at;
    f_params := args_A1____a_ilen_read_upto8_at;
    f_body := body_A1____a_ilen_read_upto8_at;
    f_tyout := tyout_A1____a_ilen_read_upto8_at;
    f_res := res_A1____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
