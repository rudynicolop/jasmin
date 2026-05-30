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

(* A32____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_44 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17602).
Definition offset_35 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17603).
Definition DELTA_23 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17604).
Definition LEN_22 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17605).
Definition TRAIL_13 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17606).
Definition CUR_13 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17607).
Definition AT_31 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17608).
Definition w_30 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17609).
Definition AT32_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17610).
Definition t128_0_7 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17611).
Definition t128_1_10 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17612).

(* Signature *)
Definition tyin_A32____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 32; aword U64; aint; aint; aint; aint; aint ].
Definition args_A32____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_44.(gv)
    ; offset_35.(gv)
    ; DELTA_23.(gv)
    ; LEN_22.(gv)
    ; TRAIL_13.(gv)
    ; CUR_13.(gv)
    ; AT_31.(gv) ].
Definition tyout_A32____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A32____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_23.(gv); LEN_22.(gv); TRAIL_13.(gv); AT_31.(gv); w_30.(gv) ].

(* Body *)
Definition body_A32____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_31) (Pvar CUR_13)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_13) (Pconst (32)%Z)) (Pvar AT_31))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_22) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_13) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_30.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_2.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_31) (Pvar CUR_13)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_2) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_22)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_30.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_35) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_23))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_2.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_2) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_23.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_23) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_22.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_22) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_2))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_30.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_23.(gv)
                                                                    ; Lvar LEN_22.(gv)
                                                                    ; Lvar TRAIL_13.(gv)
                                                                    ; Lvar AT32_2.(gv)
                                                                    ; Lvar t128_1_10.(gv) ] A32____a_ilen_read_upto16_at [:: Pvar buf_44
                                                                    ; Pvar offset_35
                                                                    ; Pvar DELTA_23
                                                                    ; Pvar LEN_22
                                                                    ; Pvar TRAIL_13
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_2 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_30.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_30
                                                                    ; Pvar t128_1_10
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_23.(gv)
                                                                    ; Lvar LEN_22.(gv)
                                                                    ; Lvar TRAIL_13.(gv)
                                                                    ; Lvar AT32_2.(gv)
                                                                    ; Lvar t128_0_7.(gv) ] A32____a_ilen_read_upto16_at [:: Pvar buf_44
                                                                    ; Pvar offset_35
                                                                    ; Pvar DELTA_23
                                                                    ; Pvar LEN_22
                                                                    ; Pvar TRAIL_13
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_2 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_23.(gv)
                                                                    ; Lvar LEN_22.(gv)
                                                                    ; Lvar TRAIL_13.(gv)
                                                                    ; Lvar AT32_2.(gv)
                                                                    ; Lvar t128_1_10.(gv) ] A32____a_ilen_read_upto16_at [:: Pvar buf_44
                                                                    ; Pvar offset_35
                                                                    ; Pvar DELTA_23
                                                                    ; Pvar LEN_22
                                                                    ; Pvar TRAIL_13
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_2 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_30.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_10)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_7) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_31.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_13) (Pvar AT32_2))) ]) ].

Definition fd_A32____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____a_ilen_read_upto32_at;
    f_params := args_A32____a_ilen_read_upto32_at;
    f_body := body_A32____a_ilen_read_upto32_at;
    f_tyout := tyout_A32____a_ilen_read_upto32_at;
    f_res := res_A32____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
