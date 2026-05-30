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

(* A2____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_30 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17984).
Definition offset_18 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17985).
Definition DELTA_12 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17986).
Definition LEN_15 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17987).
Definition TRAIL_9 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17988).
Definition CUR_9 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17989).
Definition AT_21 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17990).
Definition w_20 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17991).
Definition AT32_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17992).
Definition t128_0_5 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17993).
Definition t128_1_7 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17994).

(* Signature *)
Definition tyin_A2____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aint; aint; aint ].
Definition args_A2____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_30.(gv)
    ; offset_18.(gv)
    ; DELTA_12.(gv)
    ; LEN_15.(gv)
    ; TRAIL_9.(gv)
    ; CUR_9.(gv)
    ; AT_21.(gv) ].
Definition tyout_A2____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A2____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_12.(gv); LEN_15.(gv); TRAIL_9.(gv); AT_21.(gv); w_20.(gv) ].

(* Body *)
Definition body_A2____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_21) (Pvar CUR_9)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_9) (Pconst (32)%Z)) (Pvar AT_21))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_9) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_20.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_1.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_21) (Pvar CUR_9)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_1) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_15)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_20.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_30 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_12))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_1.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_1) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_12.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_12) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_1))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_20.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_12.(gv)
                                                                    ; Lvar LEN_15.(gv)
                                                                    ; Lvar TRAIL_9.(gv)
                                                                    ; Lvar AT32_1.(gv)
                                                                    ; Lvar t128_1_7.(gv) ] A2____a_ilen_read_upto16_at [:: Pvar buf_30
                                                                    ; Pvar offset_18
                                                                    ; Pvar DELTA_12
                                                                    ; Pvar LEN_15
                                                                    ; Pvar TRAIL_9
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_1 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_20.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_20
                                                                    ; Pvar t128_1_7
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_12.(gv)
                                                                    ; Lvar LEN_15.(gv)
                                                                    ; Lvar TRAIL_9.(gv)
                                                                    ; Lvar AT32_1.(gv)
                                                                    ; Lvar t128_0_5.(gv) ] A2____a_ilen_read_upto16_at [:: Pvar buf_30
                                                                    ; Pvar offset_18
                                                                    ; Pvar DELTA_12
                                                                    ; Pvar LEN_15
                                                                    ; Pvar TRAIL_9
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_1 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_12.(gv)
                                                                    ; Lvar LEN_15.(gv)
                                                                    ; Lvar TRAIL_9.(gv)
                                                                    ; Lvar AT32_1.(gv)
                                                                    ; Lvar t128_1_7.(gv) ] A2____a_ilen_read_upto16_at [:: Pvar buf_30
                                                                    ; Pvar offset_18
                                                                    ; Pvar DELTA_12
                                                                    ; Pvar LEN_15
                                                                    ; Pvar TRAIL_9
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_1 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_20.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_7)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_5) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_21.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_9) (Pvar AT32_1))) ]) ].

Definition fd_A2____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_ilen_read_upto32_at;
    f_params := args_A2____a_ilen_read_upto32_at;
    f_body := body_A2____a_ilen_read_upto32_at;
    f_tyout := tyout_A2____a_ilen_read_upto32_at;
    f_res := res_A2____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
