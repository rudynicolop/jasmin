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

(* ABUFLEN____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_14727 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14727).
Definition offset_14728 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14728).
Definition DELTA_14729 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14729).
Definition LEN_14730 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14730).
Definition TRAIL_14731 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14731).
Definition CUR_14732 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14732).
Definition AT_14733 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14733).
Definition w_14734 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14734).
Definition AT8_14735 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14735).
Definition t16_14736 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14736).
Definition t8_14737 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14737).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aint; aint; aint ].
Definition args_ABUFLEN____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_14727.(gv)
    ; offset_14728.(gv)
    ; DELTA_14729.(gv)
    ; LEN_14730.(gv)
    ; TRAIL_14731.(gv)
    ; CUR_14732.(gv)
    ; AT_14733.(gv) ].
Definition tyout_ABUFLEN____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_ABUFLEN____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_14729.(gv)
    ; LEN_14730.(gv)
    ; TRAIL_14731.(gv)
    ; AT_14733.(gv)
    ; w_14734.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_14733) (Pvar CUR_14732)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_14732) (Pconst (8)%Z)) (Pvar AT_14733))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_14730) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_14731) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_14734.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_14735.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_14733) (Pvar CUR_14732)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_14730))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_14734.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_14727 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14728) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14729))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_14734.(gv) ] __SHLQ [:: Pvar w_14734
                                                                    ; Pvar AT8_14735 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_14729.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14729) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_14735))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_14730.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14730) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_14735))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_14735.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_14730))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_14734.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_14727 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14728) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14729)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_14734.(gv) ] __SHLQ [:: Pvar w_14734
                                                                    ; Pvar AT8_14735 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_14729.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14729) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_14735)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_14735)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_14730.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14730) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_14735)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_14735)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_14735.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_14735)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_14735)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_14734.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_14735) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_14730)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_14736.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_14727 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14728) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14729)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_14729.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14729) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_14735)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_14735)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_14730.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14730) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_14735)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_14735)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_14736.(gv) ] __SHLQ [:: Pvar t16_14736
                                                                    ; Pvar AT8_14735 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_14734.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_14734) (Pvar t16_14736)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_14735.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_14735)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_14735)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_14735) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_14730))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_14737.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_14727 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14728) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14729)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_14737.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_14737) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_14731) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_14729.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14729) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_14730.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14730) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_14737.(gv) ] __SHLQ [:: Pvar t8_14737
                                                                    ; Pvar AT8_14735 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_14734.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_14734) (Pvar t8_14737)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_14735.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_14735) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_14735) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_14731) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_14735.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_14735) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_14731.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_14731) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_14737.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_14731) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_14737.(gv) ] __SHLQ [:: Pvar t8_14737
                                                                    ; Pvar AT8_14735 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_14734.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_14734) (Pvar t8_14737)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_14731.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_14735.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_14735) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_14733.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_14732) (Pvar AT8_14735))) ]) ].

Definition fd_ABUFLEN____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_read_upto8_at;
    f_params := args_ABUFLEN____a_ilen_read_upto8_at;
    f_body := body_ABUFLEN____a_ilen_read_upto8_at;
    f_tyout := tyout_ABUFLEN____a_ilen_read_upto8_at;
    f_res := res_ABUFLEN____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
