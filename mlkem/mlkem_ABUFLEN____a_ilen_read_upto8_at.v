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
Definition buf_152 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14727).
Definition offset_163 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14728).
Definition DELTA_107 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14729).
Definition LEN_76 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14730).
Definition TRAIL_43 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14731).
Definition CUR_43 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14732).
Definition AT_105 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14733).
Definition w_107 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14734).
Definition AT8_41 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14735).
Definition t16_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14736).
Definition t8_11 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14737).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aint; aint; aint ].
Definition args_ABUFLEN____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_152.(gv)
    ; offset_163.(gv)
    ; DELTA_107.(gv)
    ; LEN_76.(gv)
    ; TRAIL_43.(gv)
    ; CUR_43.(gv)
    ; AT_105.(gv) ].
Definition tyout_ABUFLEN____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_ABUFLEN____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_107.(gv); LEN_76.(gv); TRAIL_43.(gv); AT_105.(gv); w_107.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_read_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_105) (Pvar CUR_43)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_43) (Pconst (8)%Z)) (Pvar AT_105))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_76) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_43) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Cassgn (Lvar w_107.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT8_41.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_105) (Pvar CUR_43)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_76))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_107.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf_152 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_163) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_107))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_107.(gv) ] __SHLQ [:: Pvar w_107
                                                                    ; Pvar AT8_41 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_107.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_107) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_41))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_76.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_76) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_41))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_41.(gv)) AT_none (aint) (Pconst (8)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_76))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_107.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_152 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_163) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_107)))))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar w_107.(gv) ] __SHLQ [:: Pvar w_107
                                                                    ; Pvar AT8_41 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_107.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_107) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_41)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_41)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_76.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_76) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_41)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_41)) (Pconst (4)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_41.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_41)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_41)))) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar w_107.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))) ])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_41) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_76)))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar t16_10.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_152 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_163) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_107)))))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_107.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_107) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_41)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_41)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_76.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_76) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_41)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_41)) (Pconst (2)%Z))))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar t16_10.(gv) ] __SHLQ [:: Pvar t16_10
                                                                    ; Pvar AT8_41 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_107.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_107) (Pvar t16_10)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar AT8_41.(gv)) AT_none (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_41)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_41)))) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Olt (Cmp_int)) (Pvar AT8_41) (Pconst (8)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_76))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_11.(gv)) AT_none (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_152 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_163) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_107)))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar t8_11.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar t8_11) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_43) (Pconst (256)%Z))))))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar DELTA_107.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_107) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar LEN_76.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_76) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Ccall [:: Lvar t8_11.(gv) ] __SHLQ [:: Pvar t8_11
                                                                    ; Pvar AT8_41 ])
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar w_107.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_107) (Pvar t8_11)))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar AT8_41.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_41) (Pconst (1)%Z)))
                                                                ; MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_41) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_43) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_41.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_41) (Pconst (1)%Z)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_43.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                [::]) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_43) (Pconst (256)%Z)) (Pconst (0)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar t8_11.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_43) (Pconst (256)%Z))))
                                                                  ; MkI dummy_instr_info (
                                                                Ccall [:: Lvar t8_11.(gv) ] __SHLQ [:: Pvar t8_11
                                                                    ; Pvar AT8_41 ])
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar w_107.(gv)) AT_none (aword U64) (Papp2 (Olor U64) (Pvar w_107) (Pvar t8_11)))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar TRAIL_43.(gv)) AT_none (aint) (Pconst (0)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar AT8_41.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_41) (Pconst (1)%Z))) ]
                                                                [::]) ]) ]
                                                            [::]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_105.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_43) (Pvar AT8_41))) ]) ].

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
