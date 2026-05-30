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

(* A1600____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_140 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 15063).
Definition offset_148 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15064).
Definition DELTA_98 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15065).
Definition LEN_71 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15066).
Definition TRAIL_41 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15067).
Definition CUR_41 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15068).
Definition AT_97 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15069).
Definition w_99 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15070).
Definition AT32_9 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15071).
Definition t128_0_21 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15072).
Definition t128_1_31 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15073).

(* Signature *)
Definition tyin_A1600____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 1600; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1600____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_140.(gv)
    ; offset_148.(gv)
    ; DELTA_98.(gv)
    ; LEN_71.(gv)
    ; TRAIL_41.(gv)
    ; CUR_41.(gv)
    ; AT_97.(gv) ].
Definition tyout_A1600____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1600____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_98.(gv); LEN_71.(gv); TRAIL_41.(gv); AT_97.(gv); w_99.(gv) ].

(* Body *)
Definition body_A1600____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_97) (Pvar CUR_41)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_41) (Pconst (32)%Z)) (Pvar AT_97))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_71) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_41) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_99.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_9.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_97) (Pvar CUR_41)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_9) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_71)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_99.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_140 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_148) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_98))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_9.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_9) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_98.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_98) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_71.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_71) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_9))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_99.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_98.(gv)
                                                                    ; Lvar LEN_71.(gv)
                                                                    ; Lvar TRAIL_41.(gv)
                                                                    ; Lvar AT32_9.(gv)
                                                                    ; Lvar t128_1_31.(gv) ] A1600____a_ilen_read_upto16_at [:: Pvar buf_140
                                                                    ; Pvar offset_148
                                                                    ; Pvar DELTA_98
                                                                    ; Pvar LEN_71
                                                                    ; Pvar TRAIL_41
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_9 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_99.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_99
                                                                    ; Pvar t128_1_31
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_98.(gv)
                                                                    ; Lvar LEN_71.(gv)
                                                                    ; Lvar TRAIL_41.(gv)
                                                                    ; Lvar AT32_9.(gv)
                                                                    ; Lvar t128_0_21.(gv) ] A1600____a_ilen_read_upto16_at [:: Pvar buf_140
                                                                    ; Pvar offset_148
                                                                    ; Pvar DELTA_98
                                                                    ; Pvar LEN_71
                                                                    ; Pvar TRAIL_41
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_9 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_98.(gv)
                                                                    ; Lvar LEN_71.(gv)
                                                                    ; Lvar TRAIL_41.(gv)
                                                                    ; Lvar AT32_9.(gv)
                                                                    ; Lvar t128_1_31.(gv) ] A1600____a_ilen_read_upto16_at [:: Pvar buf_140
                                                                    ; Pvar offset_148
                                                                    ; Pvar DELTA_98
                                                                    ; Pvar LEN_71
                                                                    ; Pvar TRAIL_41
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_9 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_99.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_31)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_21) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_97.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_41) (Pvar AT32_9))) ]) ].

Definition fd_A1600____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____a_ilen_read_upto32_at;
    f_params := args_A1600____a_ilen_read_upto32_at;
    f_body := body_A1600____a_ilen_read_upto32_at;
    f_tyout := tyout_A1600____a_ilen_read_upto32_at;
    f_res := res_A1600____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
