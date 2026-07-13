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

(* A1____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_16 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18366).
Definition offset_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18367).
Definition DELTA_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18368).
Definition LEN_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18369).
Definition TRAIL_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18370).
Definition CUR_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18371).
Definition AT_11 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18372).
Definition w_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18373).
Definition AT32_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18374).
Definition t128_0_3 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18375).
Definition t128_1_4 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18376).

(* Signature *)
Definition tyin_A1____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_16.(gv)
    ; offset_1.(gv)
    ; DELTA_1.(gv)
    ; LEN_8.(gv)
    ; TRAIL_5.(gv)
    ; CUR_5.(gv)
    ; AT_11.(gv) ].
Definition tyout_A1____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_1.(gv); LEN_8.(gv); TRAIL_5.(gv); AT_11.(gv); w_10.(gv) ].

(* Body *)
Definition body_A1____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_11) (Pvar CUR_5)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_5) (Pconst (32)%Z)) (Pvar AT_11))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_8) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_5) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_10.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_0.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_11) (Pvar CUR_5)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_0) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_8)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_10.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_16 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_1) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_1))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_0.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_0) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_1.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_1) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_8.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_8) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_0))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_10.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_1.(gv)
                                                                    ; Lvar LEN_8.(gv)
                                                                    ; Lvar TRAIL_5.(gv)
                                                                    ; Lvar AT32_0.(gv)
                                                                    ; Lvar t128_1_4.(gv) ] A1____a_ilen_read_upto16_at [:: Pvar buf_16
                                                                    ; Pvar offset_1
                                                                    ; Pvar DELTA_1
                                                                    ; Pvar LEN_8
                                                                    ; Pvar TRAIL_5
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_0 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_10.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_10
                                                                    ; Pvar t128_1_4
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_1.(gv)
                                                                    ; Lvar LEN_8.(gv)
                                                                    ; Lvar TRAIL_5.(gv)
                                                                    ; Lvar AT32_0.(gv)
                                                                    ; Lvar t128_0_3.(gv) ] A1____a_ilen_read_upto16_at [:: Pvar buf_16
                                                                    ; Pvar offset_1
                                                                    ; Pvar DELTA_1
                                                                    ; Pvar LEN_8
                                                                    ; Pvar TRAIL_5
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_0 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_1.(gv)
                                                                    ; Lvar LEN_8.(gv)
                                                                    ; Lvar TRAIL_5.(gv)
                                                                    ; Lvar AT32_0.(gv)
                                                                    ; Lvar t128_1_4.(gv) ] A1____a_ilen_read_upto16_at [:: Pvar buf_16
                                                                    ; Pvar offset_1
                                                                    ; Pvar DELTA_1
                                                                    ; Pvar LEN_8
                                                                    ; Pvar TRAIL_5
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_0 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_10.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_4)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_3) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_11.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_5) (Pvar AT32_0))) ]) ].

Definition fd_A1____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_ilen_read_upto32_at;
    f_params := args_A1____a_ilen_read_upto32_at;
    f_body := body_A1____a_ilen_read_upto32_at;
    f_tyout := tyout_A1____a_ilen_read_upto32_at;
    f_res := res_A1____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
