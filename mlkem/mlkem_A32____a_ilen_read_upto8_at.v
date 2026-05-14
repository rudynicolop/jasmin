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

(* A32____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_17648 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17648).
Definition offset_17649 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17649).
Definition DELTA_17650 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17650).
Definition LEN_17651 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17651).
Definition TRAIL_17652 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17652).
Definition CUR_17653 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17653).
Definition AT_17654 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17654).
Definition w_17655 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17655).
Definition AT8_17656 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17656).
Definition t16_17657 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17657).
Definition t8_17658 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17658).

(* Signature *)
Definition tyin_A32____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 32; aword U64; aint; aint; aint; aint; aint ].
Definition args_A32____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_17648.(gv)
    ; offset_17649.(gv)
    ; DELTA_17650.(gv)
    ; LEN_17651.(gv)
    ; TRAIL_17652.(gv)
    ; CUR_17653.(gv)
    ; AT_17654.(gv) ].
Definition tyout_A32____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A32____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_17650.(gv)
    ; LEN_17651.(gv)
    ; TRAIL_17652.(gv)
    ; AT_17654.(gv)
    ; w_17655.(gv) ].

(* Body *)
Definition body_A32____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_17654) (Pvar CUR_17653)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_17653) (Pconst (8)%Z)) (Pvar AT_17654))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_17651) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_17652) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_17655.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_17656.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17654) (Pvar CUR_17653)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_17651))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_17655.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_17648 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17649) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17650))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_17655.(gv) ] __SHLQ [:: Pvar w_17655
                                                                    ; Pvar AT8_17656 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_17650.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17650) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17656))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_17651.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17651) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17656))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_17656.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_17651))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_17655.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_17648 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17649) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17650)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_17655.(gv) ] __SHLQ [:: Pvar w_17655
                                                                    ; Pvar AT8_17656 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_17650.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17650) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_17656)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17656)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_17651.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17651) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_17656)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17656)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_17656.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_17656)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_17656)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_17655.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_17656) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_17651)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_17657.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_17648 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17649) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17650)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_17650.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17650) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_17656)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17656)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_17651.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17651) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_17656)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17656)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_17657.(gv) ] __SHLQ [:: Pvar t16_17657
                                                                    ; Pvar AT8_17656 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_17655.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_17655) (Pvar t16_17657)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_17656.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_17656)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_17656)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_17656) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_17651))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_17658.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_17648 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17649) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17650)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_17658.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_17658) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_17652) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_17650.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17650) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_17651.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17651) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_17658.(gv) ] __SHLQ [:: Pvar t8_17658
                                                                    ; Pvar AT8_17656 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_17655.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_17655) (Pvar t8_17658)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_17656.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_17656) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_17656) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_17652) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_17656.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_17656) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_17652.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_17652) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_17658.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_17652) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_17658.(gv) ] __SHLQ [:: Pvar t8_17658
                                                                    ; Pvar AT8_17656 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_17655.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_17655) (Pvar t8_17658)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_17652.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_17656.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_17656) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_17654.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_17653) (Pvar AT8_17656))) ]) ].

Definition fd_A32____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____a_ilen_read_upto8_at;
    f_params := args_A32____a_ilen_read_upto8_at;
    f_body := body_A32____a_ilen_read_upto8_at;
    f_tyout := tyout_A32____a_ilen_read_upto8_at;
    f_res := res_A32____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
