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

(* A1600____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_15086 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 15086).
Definition offset_15087 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15087).
Definition DELTA_15088 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15088).
Definition LEN_15089 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15089).
Definition TRAIL_15090 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15090).
Definition CUR_15091 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15091).
Definition AT_15092 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15092).
Definition w_15093 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15093).
Definition AT16_15094 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15094).
Definition t64_0_15095 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15095).
Definition t64_1_15096 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15096).

(* Signature *)
Definition tyin_A1600____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 1600; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1600____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_15086.(gv)
    ; offset_15087.(gv)
    ; DELTA_15088.(gv)
    ; LEN_15089.(gv)
    ; TRAIL_15090.(gv)
    ; CUR_15091.(gv)
    ; AT_15092.(gv) ].
Definition tyout_A1600____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A1600____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_15088.(gv)
    ; LEN_15089.(gv)
    ; TRAIL_15090.(gv)
    ; AT_15092.(gv)
    ; w_15093.(gv) ].

(* Body *)
Definition body_A1600____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15092) (Pvar CUR_15091)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15091) (Pconst (16)%Z)) (Pvar AT_15092))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15089) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15090) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_15093.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_15094.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15092) (Pvar CUR_15091)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_15089))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_15093.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_15086 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15087) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15088))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_15093.(gv) ] __SHLDQ [:: Pvar w_15093
                                                                    ; Pvar AT16_15094 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15088.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15088) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_15094))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15089.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15089) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_15094))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_15094.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_15094))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15093.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15088.(gv)
                                                                    ; Lvar LEN_15089.(gv)
                                                                    ; Lvar TRAIL_15090.(gv)
                                                                    ; Lvar AT16_15094.(gv)
                                                                    ; Lvar t64_1_15096.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_15086
                                                                    ; Pvar offset_15087
                                                                    ; Pvar DELTA_15088
                                                                    ; Pvar LEN_15089
                                                                    ; Pvar TRAIL_15090
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_15094 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15093.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_15093
                                                                    ; Pvar t64_1_15096
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15088.(gv)
                                                                    ; Lvar LEN_15089.(gv)
                                                                    ; Lvar TRAIL_15090.(gv)
                                                                    ; Lvar AT16_15094.(gv)
                                                                    ; Lvar t64_0_15095.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_15086
                                                                    ; Pvar offset_15087
                                                                    ; Pvar DELTA_15088
                                                                    ; Pvar LEN_15089
                                                                    ; Pvar TRAIL_15090
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_15094 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_15093.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_15095)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15088.(gv)
                                                                    ; Lvar LEN_15089.(gv)
                                                                    ; Lvar TRAIL_15090.(gv)
                                                                    ; Lvar AT16_15094.(gv)
                                                                    ; Lvar t64_1_15096.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_15086
                                                                    ; Pvar offset_15087
                                                                    ; Pvar DELTA_15088
                                                                    ; Pvar LEN_15089
                                                                    ; Pvar TRAIL_15090
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_15094 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15093.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_15093
                                                                    ; Pvar t64_1_15096
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15092.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15091) (Pvar AT16_15094))) ]) ].

Definition fd_A1600____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____a_ilen_read_upto16_at;
    f_params := args_A1600____a_ilen_read_upto16_at;
    f_body := body_A1600____a_ilen_read_upto16_at;
    f_tyout := tyout_A1600____a_ilen_read_upto16_at;
    f_res := res_A1600____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
