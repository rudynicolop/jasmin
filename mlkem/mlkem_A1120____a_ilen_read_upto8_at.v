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

(* A1120____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_15491 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15491).
Definition offset_15492 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15492).
Definition DELTA_15493 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15493).
Definition LEN_15494 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15494).
Definition TRAIL_15495 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15495).
Definition CUR_15496 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15496).
Definition AT_15497 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15497).
Definition w_15498 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15498).
Definition AT8_15499 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15499).
Definition t16_15500 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15500).
Definition t8_15501 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15501).

(* Signature *)
Definition tyin_A1120____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 1120; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1120____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_15491.(gv)
    ; offset_15492.(gv)
    ; DELTA_15493.(gv)
    ; LEN_15494.(gv)
    ; TRAIL_15495.(gv)
    ; CUR_15496.(gv)
    ; AT_15497.(gv) ].
Definition tyout_A1120____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A1120____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_15493.(gv)
    ; LEN_15494.(gv)
    ; TRAIL_15495.(gv)
    ; AT_15497.(gv)
    ; w_15498.(gv) ].

(* Body *)
Definition body_A1120____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15497) (Pvar CUR_15496)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15496) (Pconst (8)%Z)) (Pvar AT_15497))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15494) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15495) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_15498.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_15499.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15497) (Pvar CUR_15496)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_15494))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_15498.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_15491 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15492) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15493))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_15498.(gv) ] __SHLQ [:: Pvar w_15498
                                                                    ; Pvar AT8_15499 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15493.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15493) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15499))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15494.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15494) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15499))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_15499.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_15494))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_15498.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_15491 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15492) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15493)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_15498.(gv) ] __SHLQ [:: Pvar w_15498
                                                                    ; Pvar AT8_15499 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_15493.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15493) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15499)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15499)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_15494.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15494) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15499)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15499)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_15499.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15499)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15499)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_15498.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_15499) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_15494)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_15500.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_15491 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15492) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15493)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_15493.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15493) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15499)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15499)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_15494.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15494) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15499)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15499)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_15500.(gv) ] __SHLQ [:: Pvar t16_15500
                                                                    ; Pvar AT8_15499 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_15498.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_15498) (Pvar t16_15500)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_15499.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15499)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15499)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_15499) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_15494))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_15501.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_15491 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15492) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15493)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_15501.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_15501) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15495) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_15493.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15493) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_15494.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15494) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_15501.(gv) ] __SHLQ [:: Pvar t8_15501
                                                                    ; Pvar AT8_15499 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_15498.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_15498) (Pvar t8_15501)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_15499.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15499) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_15499) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15495) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_15499.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15499) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_15495.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15495) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_15501.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15495) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_15501.(gv) ] __SHLQ [:: Pvar t8_15501
                                                                    ; Pvar AT8_15499 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_15498.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_15498) (Pvar t8_15501)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_15495.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_15499.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15499) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15497.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15496) (Pvar AT8_15499))) ]) ].

Definition fd_A1120____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____a_ilen_read_upto8_at;
    f_params := args_A1120____a_ilen_read_upto8_at;
    f_body := body_A1120____a_ilen_read_upto8_at;
    f_tyout := tyout_A1120____a_ilen_read_upto8_at;
    f_res := res_A1120____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
