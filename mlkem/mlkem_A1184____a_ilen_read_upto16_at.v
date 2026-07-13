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

(* A1184____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_97 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16232).
Definition offset_96 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16233).
Definition DELTA_64 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16234).
Definition LEN_49 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16235).
Definition TRAIL_28 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16236).
Definition CUR_28 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16237).
Definition AT_66 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16238).
Definition w_68 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16239).
Definition AT16_6 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16240).
Definition t64_0_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16241).
Definition t64_1_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16242).

(* Signature *)
Definition tyin_A1184____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 1184; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1184____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_97.(gv)
    ; offset_96.(gv)
    ; DELTA_64.(gv)
    ; LEN_49.(gv)
    ; TRAIL_28.(gv)
    ; CUR_28.(gv)
    ; AT_66.(gv) ].
Definition tyout_A1184____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A1184____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_64.(gv); LEN_49.(gv); TRAIL_28.(gv); AT_66.(gv); w_68.(gv) ].

(* Body *)
Definition body_A1184____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_66) (Pvar CUR_28)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_28) (Pconst (16)%Z)) (Pvar AT_66))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_49) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_28) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_68.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_6.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_66) (Pvar CUR_28)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_49))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_68.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_97 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_96) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_64))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_68.(gv) ] __SHLDQ [:: Pvar w_68
                                                                    ; Pvar AT16_6 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_64.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_64) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_6))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_49.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_49) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_6))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_6.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_6))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_68.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_64.(gv)
                                                                    ; Lvar LEN_49.(gv)
                                                                    ; Lvar TRAIL_28.(gv)
                                                                    ; Lvar AT16_6.(gv)
                                                                    ; Lvar t64_1_6.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_97
                                                                    ; Pvar offset_96
                                                                    ; Pvar DELTA_64
                                                                    ; Pvar LEN_49
                                                                    ; Pvar TRAIL_28
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_6 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_68.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_68
                                                                    ; Pvar t64_1_6
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_64.(gv)
                                                                    ; Lvar LEN_49.(gv)
                                                                    ; Lvar TRAIL_28.(gv)
                                                                    ; Lvar AT16_6.(gv)
                                                                    ; Lvar t64_0_6.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_97
                                                                    ; Pvar offset_96
                                                                    ; Pvar DELTA_64
                                                                    ; Pvar LEN_49
                                                                    ; Pvar TRAIL_28
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_6 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_68.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_6)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_64.(gv)
                                                                    ; Lvar LEN_49.(gv)
                                                                    ; Lvar TRAIL_28.(gv)
                                                                    ; Lvar AT16_6.(gv)
                                                                    ; Lvar t64_1_6.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_97
                                                                    ; Pvar offset_96
                                                                    ; Pvar DELTA_64
                                                                    ; Pvar LEN_49
                                                                    ; Pvar TRAIL_28
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_6 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_68.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_68
                                                                    ; Pvar t64_1_6
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_66.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_28) (Pvar AT16_6))) ]) ].

Definition fd_A1184____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____a_ilen_read_upto16_at;
    f_params := args_A1184____a_ilen_read_upto16_at;
    f_body := body_A1184____a_ilen_read_upto16_at;
    f_tyout := tyout_A1184____a_ilen_read_upto16_at;
    f_res := res_A1184____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
