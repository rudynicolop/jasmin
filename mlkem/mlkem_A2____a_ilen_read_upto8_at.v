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

(* A2____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_28 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 18030).
Definition offset_16 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18031).
Definition DELTA_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18032).
Definition LEN_13 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18033).
Definition TRAIL_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18034).
Definition CUR_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18035).
Definition AT_19 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18036).
Definition w_18 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18037).
Definition AT8_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18038).
Definition t16_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18039).
Definition t8_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18040).

(* Signature *)
Definition tyin_A2____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aint; aint; aint ].
Definition args_A2____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_28.(gv)
    ; offset_16.(gv)
    ; DELTA_10.(gv)
    ; LEN_13.(gv)
    ; TRAIL_7.(gv)
    ; CUR_7.(gv)
    ; AT_19.(gv) ].
Definition tyout_A2____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A2____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_10.(gv); LEN_13.(gv); TRAIL_7.(gv); AT_19.(gv); w_18.(gv) ].

(* Body *)
Definition body_A2____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_19) (Pvar CUR_7)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_7) (Pconst (8)%Z)) (Pvar AT_19))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_13) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_7) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_18.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_7.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_19) (Pvar CUR_7)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_13))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_18.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_28 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_10))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_18.(gv) ] __SHLQ [:: Pvar w_18
                                                                    ; Pvar AT8_7 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_10.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_10) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_7))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_13.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_13) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_7))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_7.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_13))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_18.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_28 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_10)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_18.(gv) ] __SHLQ [:: Pvar w_18
                                                                    ; Pvar AT8_7 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_10.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_10) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_7)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_7)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_13.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_13) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_7)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_7)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_7.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_7)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_7)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_18.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_7) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_13)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_1.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_28 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_10)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_10.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_10) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_7)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_7)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_13.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_13) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_7)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_7)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_1.(gv) ] __SHLQ [:: Pvar t16_1
                                                                    ; Pvar AT8_7 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_18.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_18) (Pvar t16_1)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_7.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_7)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_7)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_7) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_13))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_2.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_28 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_10)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_2.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_2) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_7) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_10.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_10) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_13.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_13) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_2.(gv) ] __SHLQ [:: Pvar t8_2
                                                                    ; Pvar AT8_7 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_18.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_18) (Pvar t8_2)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_7.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_7) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_7) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_7) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_7.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_7) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_7.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_7) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_2.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_7) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_2.(gv) ] __SHLQ [:: Pvar t8_2
                                                                    ; Pvar AT8_7 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_18.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_18) (Pvar t8_2)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_7.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_7.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_7) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_19.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_7) (Pvar AT8_7))) ]) ].

Definition fd_A2____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_ilen_read_upto8_at;
    f_params := args_A2____a_ilen_read_upto8_at;
    f_body := body_A2____a_ilen_read_upto8_at;
    f_tyout := tyout_A2____a_ilen_read_upto8_at;
    f_res := res_A2____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
