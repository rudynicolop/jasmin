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

(* A33____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_56 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17266).
Definition offset_50 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17267).
Definition DELTA_32 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17268).
Definition LEN_27 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17269).
Definition TRAIL_15 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17270).
Definition CUR_15 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17271).
Definition AT_39 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17272).
Definition w_38 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17273).
Definition AT8_15 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17274).
Definition t16_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17275).
Definition t8_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17276).

(* Signature *)
Definition tyin_A33____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aint; aint; aint ].
Definition args_A33____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_56.(gv)
    ; offset_50.(gv)
    ; DELTA_32.(gv)
    ; LEN_27.(gv)
    ; TRAIL_15.(gv)
    ; CUR_15.(gv)
    ; AT_39.(gv) ].
Definition tyout_A33____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A33____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_32.(gv); LEN_27.(gv); TRAIL_15.(gv); AT_39.(gv); w_38.(gv) ].

(* Body *)
Definition body_A33____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_39) (Pvar CUR_15)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15) (Pconst (8)%Z)) (Pvar AT_39))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_27) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_38.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_15.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_39) (Pvar CUR_15)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_27))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_38.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_56 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_50) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_32))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_38.(gv) ] __SHLQ [:: Pvar w_38
                                                                    ; Pvar AT8_15 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_32.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_32) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_27.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_27) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_15.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_27))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_38.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_56 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_50) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_32)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_38.(gv) ] __SHLQ [:: Pvar w_38
                                                                    ; Pvar AT8_15 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_32.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_32) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_27.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_27) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_15.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_38.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_15) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_27)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_3.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_56 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_50) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_32)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_32.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_32) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_27.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_27) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_3.(gv) ] __SHLQ [:: Pvar t16_3
                                                                    ; Pvar AT8_15 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_38.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_38) (Pvar t16_3)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_15.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_15) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_27))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_4.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_56 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_50) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_32)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_4.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_4) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_32.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_32) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_27.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_27) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_4.(gv) ] __SHLQ [:: Pvar t8_4
                                                                    ; Pvar AT8_15 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_38.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_38) (Pvar t8_4)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_15.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_15) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_15.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_15.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_4.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_4.(gv) ] __SHLQ [:: Pvar t8_4
                                                                    ; Pvar AT8_15 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_38.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_38) (Pvar t8_4)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_15.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_15.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_39.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15) (Pvar AT8_15))) ]) ].

Definition fd_A33____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_ilen_read_upto8_at;
    f_params := args_A33____a_ilen_read_upto8_at;
    f_body := body_A33____a_ilen_read_upto8_at;
    f_tyout := tyout_A33____a_ilen_read_upto8_at;
    f_res := res_A33____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
