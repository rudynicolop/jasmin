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

(* A1184____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_98 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16209).
Definition offset_97 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16210).
Definition DELTA_65 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16211).
Definition LEN_50 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16212).
Definition TRAIL_29 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16213).
Definition CUR_29 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16214).
Definition AT_67 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16215).
Definition w_69 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16216).
Definition AT32_6 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16217).
Definition t128_0_15 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16218).
Definition t128_1_22 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16219).

(* Signature *)
Definition tyin_A1184____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 1184; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1184____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_98.(gv)
    ; offset_97.(gv)
    ; DELTA_65.(gv)
    ; LEN_50.(gv)
    ; TRAIL_29.(gv)
    ; CUR_29.(gv)
    ; AT_67.(gv) ].
Definition tyout_A1184____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1184____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_65.(gv); LEN_50.(gv); TRAIL_29.(gv); AT_67.(gv); w_69.(gv) ].

(* Body *)
Definition body_A1184____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_67) (Pvar CUR_29)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_29) (Pconst (32)%Z)) (Pvar AT_67))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_50) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_29) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_69.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_6.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_67) (Pvar CUR_29)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_6) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_50)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_69.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_97) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_65))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_6.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_6) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_65.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_65) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_50.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_50) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_6))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_69.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_65.(gv)
                                                                    ; Lvar LEN_50.(gv)
                                                                    ; Lvar TRAIL_29.(gv)
                                                                    ; Lvar AT32_6.(gv)
                                                                    ; Lvar t128_1_22.(gv) ] A1184____a_ilen_read_upto16_at [:: Pvar buf_98
                                                                    ; Pvar offset_97
                                                                    ; Pvar DELTA_65
                                                                    ; Pvar LEN_50
                                                                    ; Pvar TRAIL_29
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_6 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_69.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_69
                                                                    ; Pvar t128_1_22
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_65.(gv)
                                                                    ; Lvar LEN_50.(gv)
                                                                    ; Lvar TRAIL_29.(gv)
                                                                    ; Lvar AT32_6.(gv)
                                                                    ; Lvar t128_0_15.(gv) ] A1184____a_ilen_read_upto16_at [:: Pvar buf_98
                                                                    ; Pvar offset_97
                                                                    ; Pvar DELTA_65
                                                                    ; Pvar LEN_50
                                                                    ; Pvar TRAIL_29
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_6 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_65.(gv)
                                                                    ; Lvar LEN_50.(gv)
                                                                    ; Lvar TRAIL_29.(gv)
                                                                    ; Lvar AT32_6.(gv)
                                                                    ; Lvar t128_1_22.(gv) ] A1184____a_ilen_read_upto16_at [:: Pvar buf_98
                                                                    ; Pvar offset_97
                                                                    ; Pvar DELTA_65
                                                                    ; Pvar LEN_50
                                                                    ; Pvar TRAIL_29
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_6 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_69.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_22)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_15) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_67.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_29) (Pvar AT32_6))) ]) ].

Definition fd_A1184____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____a_ilen_read_upto32_at;
    f_params := args_A1184____a_ilen_read_upto32_at;
    f_body := body_A1184____a_ilen_read_upto32_at;
    f_tyout := tyout_A1184____a_ilen_read_upto32_at;
    f_res := res_A1184____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
