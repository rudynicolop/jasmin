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
Definition buf_139 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 15086).
Definition offset_147 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15087).
Definition DELTA_97 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15088).
Definition LEN_70 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15089).
Definition TRAIL_40 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15090).
Definition CUR_40 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15091).
Definition AT_96 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15092).
Definition w_98 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15093).
Definition AT16_9 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15094).
Definition t64_0_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15095).
Definition t64_1_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15096).

(* Signature *)
Definition tyin_A1600____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 1600; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1600____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_139.(gv)
    ; offset_147.(gv)
    ; DELTA_97.(gv)
    ; LEN_70.(gv)
    ; TRAIL_40.(gv)
    ; CUR_40.(gv)
    ; AT_96.(gv) ].
Definition tyout_A1600____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A1600____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_97.(gv); LEN_70.(gv); TRAIL_40.(gv); AT_96.(gv); w_98.(gv) ].

(* Body *)
Definition body_A1600____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_96) (Pvar CUR_40)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_40) (Pconst (16)%Z)) (Pvar AT_96))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_70) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_40) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_98.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_9.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_96) (Pvar CUR_40)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_70))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_98.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_139 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_147) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_97))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_98.(gv) ] __SHLDQ [:: Pvar w_98
                                                                    ; Pvar AT16_9 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_97.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_97) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_9))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_70.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_70) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_9))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_9.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_9))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_98.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_97.(gv)
                                                                    ; Lvar LEN_70.(gv)
                                                                    ; Lvar TRAIL_40.(gv)
                                                                    ; Lvar AT16_9.(gv)
                                                                    ; Lvar t64_1_9.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_139
                                                                    ; Pvar offset_147
                                                                    ; Pvar DELTA_97
                                                                    ; Pvar LEN_70
                                                                    ; Pvar TRAIL_40
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_9 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_98.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_98
                                                                    ; Pvar t64_1_9
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_97.(gv)
                                                                    ; Lvar LEN_70.(gv)
                                                                    ; Lvar TRAIL_40.(gv)
                                                                    ; Lvar AT16_9.(gv)
                                                                    ; Lvar t64_0_9.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_139
                                                                    ; Pvar offset_147
                                                                    ; Pvar DELTA_97
                                                                    ; Pvar LEN_70
                                                                    ; Pvar TRAIL_40
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_9 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_98.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_9)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_97.(gv)
                                                                    ; Lvar LEN_70.(gv)
                                                                    ; Lvar TRAIL_40.(gv)
                                                                    ; Lvar AT16_9.(gv)
                                                                    ; Lvar t64_1_9.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf_139
                                                                    ; Pvar offset_147
                                                                    ; Pvar DELTA_97
                                                                    ; Pvar LEN_70
                                                                    ; Pvar TRAIL_40
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_9 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_98.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_98
                                                                    ; Pvar t64_1_9
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_96.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_40) (Pvar AT16_9))) ]) ].

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
