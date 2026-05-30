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

(* A33____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_58 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17220).
Definition offset_52 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17221).
Definition DELTA_34 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17222).
Definition LEN_29 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17223).
Definition TRAIL_17 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17224).
Definition CUR_17 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17225).
Definition AT_41 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17226).
Definition w_40 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17227).
Definition AT32_3 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17228).
Definition t128_0_9 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17229).
Definition t128_1_13 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17230).

(* Signature *)
Definition tyin_A33____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aint; aint; aint ].
Definition args_A33____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_58.(gv)
    ; offset_52.(gv)
    ; DELTA_34.(gv)
    ; LEN_29.(gv)
    ; TRAIL_17.(gv)
    ; CUR_17.(gv)
    ; AT_41.(gv) ].
Definition tyout_A33____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A33____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_34.(gv); LEN_29.(gv); TRAIL_17.(gv); AT_41.(gv); w_40.(gv) ].

(* Body *)
Definition body_A33____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_41) (Pvar CUR_17)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_17) (Pconst (32)%Z)) (Pvar AT_41))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_29) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_17) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_40.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_3.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_41) (Pvar CUR_17)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_3) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_29)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_40.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_58 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_52) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_34))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_3.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_3) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_34.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_34) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_29.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_29) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_3))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_40.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_34.(gv)
                                                                    ; Lvar LEN_29.(gv)
                                                                    ; Lvar TRAIL_17.(gv)
                                                                    ; Lvar AT32_3.(gv)
                                                                    ; Lvar t128_1_13.(gv) ] A33____a_ilen_read_upto16_at [:: Pvar buf_58
                                                                    ; Pvar offset_52
                                                                    ; Pvar DELTA_34
                                                                    ; Pvar LEN_29
                                                                    ; Pvar TRAIL_17
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_3 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_40.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_40
                                                                    ; Pvar t128_1_13
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_34.(gv)
                                                                    ; Lvar LEN_29.(gv)
                                                                    ; Lvar TRAIL_17.(gv)
                                                                    ; Lvar AT32_3.(gv)
                                                                    ; Lvar t128_0_9.(gv) ] A33____a_ilen_read_upto16_at [:: Pvar buf_58
                                                                    ; Pvar offset_52
                                                                    ; Pvar DELTA_34
                                                                    ; Pvar LEN_29
                                                                    ; Pvar TRAIL_17
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_3 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_34.(gv)
                                                                    ; Lvar LEN_29.(gv)
                                                                    ; Lvar TRAIL_17.(gv)
                                                                    ; Lvar AT32_3.(gv)
                                                                    ; Lvar t128_1_13.(gv) ] A33____a_ilen_read_upto16_at [:: Pvar buf_58
                                                                    ; Pvar offset_52
                                                                    ; Pvar DELTA_34
                                                                    ; Pvar LEN_29
                                                                    ; Pvar TRAIL_17
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_3 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_40.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_13)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_9) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_41.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_17) (Pvar AT32_3))) ]) ].

Definition fd_A33____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_ilen_read_upto32_at;
    f_params := args_A33____a_ilen_read_upto32_at;
    f_body := body_A33____a_ilen_read_upto32_at;
    f_tyout := tyout_A33____a_ilen_read_upto32_at;
    f_res := res_A33____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
