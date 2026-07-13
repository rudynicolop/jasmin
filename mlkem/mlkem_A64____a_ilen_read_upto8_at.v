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

(* A64____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_70 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16884).
Definition offset_67 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16885).
Definition DELTA_43 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16886).
Definition LEN_34 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16887).
Definition TRAIL_19 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16888).
Definition CUR_19 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16889).
Definition AT_49 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16890).
Definition w_48 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16891).
Definition AT8_19 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16892).
Definition t16_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16893).
Definition t8_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16894).

(* Signature *)
Definition tyin_A64____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 64; aword U64; aint; aint; aint; aint; aint ].
Definition args_A64____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_70.(gv)
    ; offset_67.(gv)
    ; DELTA_43.(gv)
    ; LEN_34.(gv)
    ; TRAIL_19.(gv)
    ; CUR_19.(gv)
    ; AT_49.(gv) ].
Definition tyout_A64____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A64____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_43.(gv); LEN_34.(gv); TRAIL_19.(gv); AT_49.(gv); w_48.(gv) ].

(* Body *)
Definition body_A64____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_49) (Pvar CUR_19)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_19) (Pconst (8)%Z)) (Pvar AT_49))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_34) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_19) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_48.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_19.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_49) (Pvar CUR_19)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_34))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_48.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_70 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_67) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_43))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_48.(gv) ] __SHLQ [:: Pvar w_48
                                                                    ; Pvar AT8_19 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_43.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_43) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_19))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_34.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_34) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_19))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_19.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_34))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_48.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_70 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_67) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_43)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_48.(gv) ] __SHLQ [:: Pvar w_48
                                                                    ; Pvar AT8_19 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_43.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_43) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_19)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_19)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_34.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_34) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_19)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_19)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_19.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_19)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_19)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_48.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_19) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_34)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_4.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_70 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_67) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_43)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_43.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_43) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_19)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_19)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_34.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_34) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_19)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_19)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_4.(gv) ] __SHLQ [:: Pvar t16_4
                                                                    ; Pvar AT8_19 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_48.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_48) (Pvar t16_4)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_19.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_19)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_19)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_19) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_34))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_5.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_70 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_67) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_43)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_5.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_5) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_19) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_43.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_43) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_34.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_34) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_5.(gv) ] __SHLQ [:: Pvar t8_5
                                                                    ; Pvar AT8_19 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_48.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_48) (Pvar t8_5)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_19.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_19) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_19) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_19) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_19.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_19) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_19.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_19) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_5.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_19) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_5.(gv) ] __SHLQ [:: Pvar t8_5
                                                                    ; Pvar AT8_19 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_48.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_48) (Pvar t8_5)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_19.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_19.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_19) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_49.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_19) (Pvar AT8_19))) ]) ].

Definition fd_A64____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_ilen_read_upto8_at;
    f_params := args_A64____a_ilen_read_upto8_at;
    f_body := body_A64____a_ilen_read_upto8_at;
    f_tyout := tyout_A64____a_ilen_read_upto8_at;
    f_res := res_A64____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
