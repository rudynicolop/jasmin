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

(* ABUFLEN____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_154 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14681).
Definition offset_165 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14682).
Definition DELTA_109 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14683).
Definition LEN_78 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14684).
Definition TRAIL_45 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14685).
Definition CUR_45 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14686).
Definition AT_107 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14687).
Definition w_109 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14688).
Definition AT32_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14689).
Definition t128_0_23 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14690).
Definition t128_1_34 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14691).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aint; aint; aint ].
Definition args_ABUFLEN____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_154.(gv)
    ; offset_165.(gv)
    ; DELTA_109.(gv)
    ; LEN_78.(gv)
    ; TRAIL_45.(gv)
    ; CUR_45.(gv)
    ; AT_107.(gv) ].
Definition tyout_ABUFLEN____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_ABUFLEN____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_109.(gv); LEN_78.(gv); TRAIL_45.(gv); AT_107.(gv); w_109.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_107) (Pvar CUR_45)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_45) (Pconst (32)%Z)) (Pvar AT_107))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_78) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_45) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_109.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_10.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_107) (Pvar CUR_45)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_10) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_78)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_109.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_154 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_165) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_109))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_10.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_10) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_109.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_109) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_78.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_78) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_10))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_109.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_109.(gv)
                                                                    ; Lvar LEN_78.(gv)
                                                                    ; Lvar TRAIL_45.(gv)
                                                                    ; Lvar AT32_10.(gv)
                                                                    ; Lvar t128_1_34.(gv) ] ABUFLEN____a_ilen_read_upto16_at [:: Pvar buf_154
                                                                    ; Pvar offset_165
                                                                    ; Pvar DELTA_109
                                                                    ; Pvar LEN_78
                                                                    ; Pvar TRAIL_45
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_10 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_109.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_109
                                                                    ; Pvar t128_1_34
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_109.(gv)
                                                                    ; Lvar LEN_78.(gv)
                                                                    ; Lvar TRAIL_45.(gv)
                                                                    ; Lvar AT32_10.(gv)
                                                                    ; Lvar t128_0_23.(gv) ] ABUFLEN____a_ilen_read_upto16_at [:: Pvar buf_154
                                                                    ; Pvar offset_165
                                                                    ; Pvar DELTA_109
                                                                    ; Pvar LEN_78
                                                                    ; Pvar TRAIL_45
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_10 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_109.(gv)
                                                                    ; Lvar LEN_78.(gv)
                                                                    ; Lvar TRAIL_45.(gv)
                                                                    ; Lvar AT32_10.(gv)
                                                                    ; Lvar t128_1_34.(gv) ] ABUFLEN____a_ilen_read_upto16_at [:: Pvar buf_154
                                                                    ; Pvar offset_165
                                                                    ; Pvar DELTA_109
                                                                    ; Pvar LEN_78
                                                                    ; Pvar TRAIL_45
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_10 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_109.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_34)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_23) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_107.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_45) (Pvar AT32_10))) ]) ].

Definition fd_ABUFLEN____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_read_upto32_at;
    f_params := args_ABUFLEN____a_ilen_read_upto32_at;
    f_body := body_ABUFLEN____a_ilen_read_upto32_at;
    f_tyout := tyout_ABUFLEN____a_ilen_read_upto32_at;
    f_res := res_ABUFLEN____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
