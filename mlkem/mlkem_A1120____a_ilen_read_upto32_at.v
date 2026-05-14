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
Definition buf_15445 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15445).
Definition offset_15446 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15446).
Definition DELTA_15447 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15447).
Definition LEN_15448 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15448).
Definition TRAIL_15449 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15449).
Definition CUR_15450 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15450).
Definition AT_15451 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15451).
Definition w_15452 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15452).
Definition AT32_15453 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15453).
Definition t128_0_15454 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15454).
Definition t128_1_15455 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15455).

(* Signature *)
Definition tyin_A1120____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 1120; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1120____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_15445.(gv)
    ; offset_15446.(gv)
    ; DELTA_15447.(gv)
    ; LEN_15448.(gv)
    ; TRAIL_15449.(gv)
    ; CUR_15450.(gv)
    ; AT_15451.(gv) ].
Definition tyout_A1120____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1120____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_15447.(gv)
    ; LEN_15448.(gv)
    ; TRAIL_15449.(gv)
    ; AT_15451.(gv)
    ; w_15452.(gv) ].

(* Body *)
Definition body_A1120____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15451) (Pvar CUR_15450)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15450) (Pconst (32)%Z)) (Pvar AT_15451))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15448) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15449) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_15452.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_15453.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15451) (Pvar CUR_15450)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_15453) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_15448)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_15452.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_15445 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15446) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15447))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_15453.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_15453) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15447.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15447) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15448.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15448) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_15453))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15452.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15447.(gv)
                                                                    ; Lvar LEN_15448.(gv)
                                                                    ; Lvar TRAIL_15449.(gv)
                                                                    ; Lvar AT32_15453.(gv)
                                                                    ; Lvar t128_1_15455.(gv) ] A1120____a_ilen_read_upto16_at [:: Pvar buf_15445
                                                                    ; Pvar offset_15446
                                                                    ; Pvar DELTA_15447
                                                                    ; Pvar LEN_15448
                                                                    ; Pvar TRAIL_15449
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_15453 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15452.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_15452
                                                                    ; Pvar t128_1_15455
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15447.(gv)
                                                                    ; Lvar LEN_15448.(gv)
                                                                    ; Lvar TRAIL_15449.(gv)
                                                                    ; Lvar AT32_15453.(gv)
                                                                    ; Lvar t128_0_15454.(gv) ] A1120____a_ilen_read_upto16_at [:: Pvar buf_15445
                                                                    ; Pvar offset_15446
                                                                    ; Pvar DELTA_15447
                                                                    ; Pvar LEN_15448
                                                                    ; Pvar TRAIL_15449
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_15453 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15447.(gv)
                                                                    ; Lvar LEN_15448.(gv)
                                                                    ; Lvar TRAIL_15449.(gv)
                                                                    ; Lvar AT32_15453.(gv)
                                                                    ; Lvar t128_1_15455.(gv) ] A1120____a_ilen_read_upto16_at [:: Pvar buf_15445
                                                                    ; Pvar offset_15446
                                                                    ; Pvar DELTA_15447
                                                                    ; Pvar LEN_15448
                                                                    ; Pvar TRAIL_15449
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_15453 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_15452.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_15455)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_15454) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15451.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15450) (Pvar AT32_15453))) ]) ].

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
