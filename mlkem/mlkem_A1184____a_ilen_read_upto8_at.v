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

(* A1184____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_96 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16255).
Definition offset_95 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16256).
Definition DELTA_63 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16257).
Definition LEN_48 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16258).
Definition TRAIL_27 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16259).
Definition CUR_27 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16260).
Definition AT_65 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16261).
Definition w_67 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16262).
Definition AT8_25 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16263).
Definition t16_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16264).
Definition t8_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16265).

(* Signature *)
Definition tyin_A1184____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 1184; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1184____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_96.(gv)
    ; offset_95.(gv)
    ; DELTA_63.(gv)
    ; LEN_48.(gv)
    ; TRAIL_27.(gv)
    ; CUR_27.(gv)
    ; AT_65.(gv) ].
Definition tyout_A1184____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A1184____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_63.(gv); LEN_48.(gv); TRAIL_27.(gv); AT_65.(gv); w_67.(gv) ].

(* Body *)
Definition body_A1184____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_65) (Pvar CUR_27)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_27) (Pconst (8)%Z)) (Pvar AT_65))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_48) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_27) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_67.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_25.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_65) (Pvar CUR_27)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_48))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_67.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_95) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_63))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_67.(gv) ] __SHLQ [:: Pvar w_67
                                                                    ; Pvar AT8_25 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_63.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_63) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_25))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_48.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_48) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_25))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_25.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_48))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_67.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_95) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_63)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_67.(gv) ] __SHLQ [:: Pvar w_67
                                                                    ; Pvar AT8_25 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_63.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_63) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_25)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_25)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_48.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_48) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_25)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_25)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_25.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_25)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_25)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_67.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_25) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_48)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_6.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_95) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_63)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_63.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_63) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_25)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_25)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_48.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_48) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_25)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_25)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_6.(gv) ] __SHLQ [:: Pvar t16_6
                                                                    ; Pvar AT8_25 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_67.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_67) (Pvar t16_6)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_25.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_25)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_25)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_25) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_48))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_7.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_95) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_63)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_7.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_7) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_27) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_63.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_63) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_48.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_48) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_7.(gv) ] __SHLQ [:: Pvar t8_7
                                                                    ; Pvar AT8_25 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_67.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_67) (Pvar t8_7)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_25.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_25) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_25) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_27) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_25.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_25) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_27.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_27) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_7.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_27) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_7.(gv) ] __SHLQ [:: Pvar t8_7
                                                                    ; Pvar AT8_25 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_67.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_67) (Pvar t8_7)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_27.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_25.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_25) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_65.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_27) (Pvar AT8_25))) ]) ].

Definition fd_A1184____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____a_ilen_read_upto8_at;
    f_params := args_A1184____a_ilen_read_upto8_at;
    f_body := body_A1184____a_ilen_read_upto8_at;
    f_tyout := tyout_A1184____a_ilen_read_upto8_at;
    f_res := res_A1184____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
