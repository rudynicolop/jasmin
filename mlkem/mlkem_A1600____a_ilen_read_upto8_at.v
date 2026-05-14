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

(* A1600____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_15109 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 15109).
Definition offset_15110 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15110).
Definition DELTA_15111 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15111).
Definition LEN_15112 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15112).
Definition TRAIL_15113 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15113).
Definition CUR_15114 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15114).
Definition AT_15115 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15115).
Definition w_15116 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15116).
Definition AT8_15117 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15117).
Definition t16_15118 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15118).
Definition t8_15119 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15119).

(* Signature *)
Definition tyin_A1600____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 1600; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1600____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_15109.(gv)
    ; offset_15110.(gv)
    ; DELTA_15111.(gv)
    ; LEN_15112.(gv)
    ; TRAIL_15113.(gv)
    ; CUR_15114.(gv)
    ; AT_15115.(gv) ].
Definition tyout_A1600____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A1600____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_15111.(gv)
    ; LEN_15112.(gv)
    ; TRAIL_15113.(gv)
    ; AT_15115.(gv)
    ; w_15116.(gv) ].

(* Body *)
Definition body_A1600____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15115) (Pvar CUR_15114)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15114) (Pconst (8)%Z)) (Pvar AT_15115))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15112) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15113) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_15116.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_15117.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15115) (Pvar CUR_15114)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_15112))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_15116.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_15109 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15110) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15111))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_15116.(gv) ] __SHLQ [:: Pvar w_15116
                                                                    ; Pvar AT8_15117 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15111.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15111) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15117))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15112.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15112) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15117))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_15117.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_15112))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_15116.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_15109 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15110) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15111)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_15116.(gv) ] __SHLQ [:: Pvar w_15116
                                                                    ; Pvar AT8_15117 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_15111.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15111) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15117)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15117)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_15112.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15112) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15117)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15117)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_15117.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15117)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15117)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_15116.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_15117) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_15112)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_15118.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_15109 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15110) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15111)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_15111.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15111) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15117)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15117)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_15112.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15112) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15117)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15117)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_15118.(gv) ] __SHLQ [:: Pvar t16_15118
                                                                    ; Pvar AT8_15117 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_15116.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_15116) (Pvar t16_15118)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_15117.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15117)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15117)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_15117) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_15112))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_15119.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_15109 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15110) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15111)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_15119.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_15119) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15113) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_15111.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15111) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_15112.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15112) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_15119.(gv) ] __SHLQ [:: Pvar t8_15119
                                                                    ; Pvar AT8_15117 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_15116.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_15116) (Pvar t8_15119)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_15117.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15117) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_15117) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15113) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_15117.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15117) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_15113.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15113) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_15119.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15113) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_15119.(gv) ] __SHLQ [:: Pvar t8_15119
                                                                    ; Pvar AT8_15117 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_15116.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_15116) (Pvar t8_15119)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_15113.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_15117.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15117) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15115.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15114) (Pvar AT8_15117))) ]) ].

Definition fd_A1600____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____a_ilen_read_upto8_at;
    f_params := args_A1600____a_ilen_read_upto8_at;
    f_body := body_A1600____a_ilen_read_upto8_at;
    f_tyout := tyout_A1600____a_ilen_read_upto8_at;
    f_res := res_A1600____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
