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

(* A128____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_16637 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16637).
Definition offset_16638 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16638).
Definition DELTA_16639 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16639).
Definition LEN_16640 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16640).
Definition TRAIL_16641 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16641).
Definition CUR_16642 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16642).
Definition AT_16643 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16643).
Definition w_16644 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16644).
Definition AT8_16645 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16645).
Definition t16_16646 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16646).
Definition t8_16647 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16647).

(* Signature *)
Definition tyin_A128____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 128; aword U64; aint; aint; aint; aint; aint ].
Definition args_A128____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_16637.(gv)
    ; offset_16638.(gv)
    ; DELTA_16639.(gv)
    ; LEN_16640.(gv)
    ; TRAIL_16641.(gv)
    ; CUR_16642.(gv)
    ; AT_16643.(gv) ].
Definition tyout_A128____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A128____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_16639.(gv)
    ; LEN_16640.(gv)
    ; TRAIL_16641.(gv)
    ; AT_16643.(gv)
    ; w_16644.(gv) ].

(* Body *)
Definition body_A128____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_16643) (Pvar CUR_16642)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_16642) (Pconst (8)%Z)) (Pvar AT_16643))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_16640) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_16641) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_16644.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_16645.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_16643) (Pvar CUR_16642)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_16640))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_16644.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_16637 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16638) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16639))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_16644.(gv) ] __SHLQ [:: Pvar w_16644
                                                                    ; Pvar AT8_16645 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_16639.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16639) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16645))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_16640.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16640) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16645))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_16645.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_16640))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_16644.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_16637 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16638) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16639)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_16644.(gv) ] __SHLQ [:: Pvar w_16644
                                                                    ; Pvar AT8_16645 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_16639.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16639) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_16645)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16645)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_16640.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16640) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_16645)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16645)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_16645.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_16645)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_16645)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_16644.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_16645) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_16640)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_16646.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_16637 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16638) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16639)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_16639.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16639) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_16645)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16645)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_16640.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16640) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_16645)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16645)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_16646.(gv) ] __SHLQ [:: Pvar t16_16646
                                                                    ; Pvar AT8_16645 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_16644.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_16644) (Pvar t16_16646)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_16645.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_16645)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_16645)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_16645) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_16640))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_16647.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_16637 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16638) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16639)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_16647.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_16647) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_16641) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_16639.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16639) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_16640.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16640) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_16647.(gv) ] __SHLQ [:: Pvar t8_16647
                                                                    ; Pvar AT8_16645 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_16644.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_16644) (Pvar t8_16647)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_16645.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_16645) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_16645) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_16641) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_16645.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_16645) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_16641.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_16641) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_16647.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_16641) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_16647.(gv) ] __SHLQ [:: Pvar t8_16647
                                                                    ; Pvar AT8_16645 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_16644.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_16644) (Pvar t8_16647)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_16641.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_16645.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_16645) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_16643.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_16642) (Pvar AT8_16645))) ]) ].

Definition fd_A128____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____a_ilen_read_upto8_at;
    f_params := args_A128____a_ilen_read_upto8_at;
    f_body := body_A128____a_ilen_read_upto8_at;
    f_tyout := tyout_A128____a_ilen_read_upto8_at;
    f_res := res_A128____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
