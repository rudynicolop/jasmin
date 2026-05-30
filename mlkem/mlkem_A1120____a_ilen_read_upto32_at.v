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

(* A1120____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_126 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15445).
Definition offset_131 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15446).
Definition DELTA_87 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15447).
Definition LEN_64 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15448).
Definition TRAIL_37 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15449).
Definition CUR_37 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15450).
Definition AT_87 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15451).
Definition w_89 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15452).
Definition AT32_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15453).
Definition t128_0_19 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15454).
Definition t128_1_28 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15455).

(* Signature *)
Definition tyin_A1120____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 1120; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1120____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_126.(gv)
    ; offset_131.(gv)
    ; DELTA_87.(gv)
    ; LEN_64.(gv)
    ; TRAIL_37.(gv)
    ; CUR_37.(gv)
    ; AT_87.(gv) ].
Definition tyout_A1120____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1120____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_87.(gv); LEN_64.(gv); TRAIL_37.(gv); AT_87.(gv); w_89.(gv) ].

(* Body *)
Definition body_A1120____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_87) (Pvar CUR_37)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_37) (Pconst (32)%Z)) (Pvar AT_87))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_64) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_37) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_89.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_8.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_87) (Pvar CUR_37)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_8) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_64)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_89.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_126 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_131) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_87))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_8.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_8) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_87.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_87) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_64.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_64) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_8))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_89.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_87.(gv)
                                                                    ; Lvar LEN_64.(gv)
                                                                    ; Lvar TRAIL_37.(gv)
                                                                    ; Lvar AT32_8.(gv)
                                                                    ; Lvar t128_1_28.(gv) ] A1120____a_ilen_read_upto16_at [:: Pvar buf_126
                                                                    ; Pvar offset_131
                                                                    ; Pvar DELTA_87
                                                                    ; Pvar LEN_64
                                                                    ; Pvar TRAIL_37
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_8 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_89.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_89
                                                                    ; Pvar t128_1_28
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_87.(gv)
                                                                    ; Lvar LEN_64.(gv)
                                                                    ; Lvar TRAIL_37.(gv)
                                                                    ; Lvar AT32_8.(gv)
                                                                    ; Lvar t128_0_19.(gv) ] A1120____a_ilen_read_upto16_at [:: Pvar buf_126
                                                                    ; Pvar offset_131
                                                                    ; Pvar DELTA_87
                                                                    ; Pvar LEN_64
                                                                    ; Pvar TRAIL_37
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_8 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_87.(gv)
                                                                    ; Lvar LEN_64.(gv)
                                                                    ; Lvar TRAIL_37.(gv)
                                                                    ; Lvar AT32_8.(gv)
                                                                    ; Lvar t128_1_28.(gv) ] A1120____a_ilen_read_upto16_at [:: Pvar buf_126
                                                                    ; Pvar offset_131
                                                                    ; Pvar DELTA_87
                                                                    ; Pvar LEN_64
                                                                    ; Pvar TRAIL_37
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_8 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_89.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_28)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_19) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_87.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_37) (Pvar AT32_8))) ]) ].

Definition fd_A1120____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____a_ilen_read_upto32_at;
    f_params := args_A1120____a_ilen_read_upto32_at;
    f_body := body_A1120____a_ilen_read_upto32_at;
    f_tyout := tyout_A1120____a_ilen_read_upto32_at;
    f_res := res_A1120____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
