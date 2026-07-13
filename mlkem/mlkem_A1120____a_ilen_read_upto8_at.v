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
Definition buf_124 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15491).
Definition offset_129 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15492).
Definition DELTA_85 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15493).
Definition LEN_62 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15494).
Definition TRAIL_35 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15495).
Definition CUR_35 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15496).
Definition AT_85 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15497).
Definition w_87 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15498).
Definition AT8_33 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15499).
Definition t16_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15500).
Definition t8_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15501).

(* Signature *)
Definition tyin_A1120____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 1120; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1120____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_124.(gv)
    ; offset_129.(gv)
    ; DELTA_85.(gv)
    ; LEN_62.(gv)
    ; TRAIL_35.(gv)
    ; CUR_35.(gv)
    ; AT_85.(gv) ].
Definition tyout_A1120____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A1120____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_85.(gv); LEN_62.(gv); TRAIL_35.(gv); AT_85.(gv); w_87.(gv) ].

(* Body *)
Definition body_A1120____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_85) (Pvar CUR_35)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_35) (Pconst (8)%Z)) (Pvar AT_85))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_62) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_35) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_87.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_33.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_85) (Pvar CUR_35)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_62))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_87.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_124 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_129) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_85))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_87.(gv) ] __SHLQ [:: Pvar w_87
                                                                    ; Pvar AT8_33 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_85.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_85) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_33))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_62.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_62) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_33))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_33.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_62))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_87.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_124 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_129) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_85)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_87.(gv) ] __SHLQ [:: Pvar w_87
                                                                    ; Pvar AT8_33 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_85.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_85) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_33)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_33)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_62.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_62) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_33)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_33)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_33.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_33)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_33)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_87.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_33) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_62)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_8.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_124 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_129) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_85)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_85.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_85) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_33)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_33)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_62.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_62) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_33)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_33)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_8.(gv) ] __SHLQ [:: Pvar t16_8
                                                                    ; Pvar AT8_33 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_87.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_87) (Pvar t16_8)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_33.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_33)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_33)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_33) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_62))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_9.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_124 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_129) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_85)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_9.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_9) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_35) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_85.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_85) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_62.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_62) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_9.(gv) ] __SHLQ [:: Pvar t8_9
                                                                    ; Pvar AT8_33 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_87.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_87) (Pvar t8_9)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_33.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_33) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_33) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_35) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_33.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_33) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_35.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_35) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_9.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_35) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_9.(gv) ] __SHLQ [:: Pvar t8_9
                                                                    ; Pvar AT8_33 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_87.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_87) (Pvar t8_9)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_35.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_33.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_33) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_85.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_35) (Pvar AT8_33))) ]) ].

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
