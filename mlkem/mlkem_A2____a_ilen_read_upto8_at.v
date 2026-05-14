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
Definition buf_18030 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 18030).
Definition offset_18031 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18031).
Definition DELTA_18032 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18032).
Definition LEN_18033 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18033).
Definition TRAIL_18034 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18034).
Definition CUR_18035 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18035).
Definition AT_18036 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18036).
Definition w_18037 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18037).
Definition AT8_18038 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18038).
Definition t16_18039 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18039).
Definition t8_18040 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18040).

(* Signature *)
Definition tyin_A2____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aint; aint; aint ].
Definition args_A2____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_18030.(gv)
    ; offset_18031.(gv)
    ; DELTA_18032.(gv)
    ; LEN_18033.(gv)
    ; TRAIL_18034.(gv)
    ; CUR_18035.(gv)
    ; AT_18036.(gv) ].
Definition tyout_A2____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A2____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_18032.(gv)
    ; LEN_18033.(gv)
    ; TRAIL_18034.(gv)
    ; AT_18036.(gv)
    ; w_18037.(gv) ].

(* Body *)
Definition body_A2____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_18036) (Pvar CUR_18035)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_18035) (Pconst (8)%Z)) (Pvar AT_18036))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_18033) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_18034) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_18037.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_18038.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_18036) (Pvar CUR_18035)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_18033))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_18037.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_18030 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18031) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18032))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_18037.(gv) ] __SHLQ [:: Pvar w_18037
                                                                    ; Pvar AT8_18038 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_18032.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18032) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18038))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_18033.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18033) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18038))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_18038.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_18033))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_18037.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_18030 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18031) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18032)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_18037.(gv) ] __SHLQ [:: Pvar w_18037
                                                                    ; Pvar AT8_18038 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_18032.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18032) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_18038)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18038)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_18033.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18033) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_18038)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18038)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_18038.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_18038)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_18038)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_18037.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_18038) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_18033)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_18039.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_18030 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18031) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18032)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_18032.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18032) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_18038)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18038)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_18033.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18033) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_18038)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_18038)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_18039.(gv) ] __SHLQ [:: Pvar t16_18039
                                                                    ; Pvar AT8_18038 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_18037.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_18037) (Pvar t16_18039)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_18038.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_18038)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_18038)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_18038) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_18033))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_18040.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_18030 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18031) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18032)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_18040.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_18040) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_18034) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_18032.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18032) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_18033.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18033) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_18040.(gv) ] __SHLQ [:: Pvar t8_18040
                                                                    ; Pvar AT8_18038 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_18037.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_18037) (Pvar t8_18040)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_18038.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_18038) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_18038) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_18034) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_18038.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_18038) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_18034.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_18034) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_18040.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_18034) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_18040.(gv) ] __SHLQ [:: Pvar t8_18040
                                                                    ; Pvar AT8_18038 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_18037.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_18037) (Pvar t8_18040)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_18034.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_18038.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_18038) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_18036.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_18035) (Pvar AT8_18038))) ]) ].

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
