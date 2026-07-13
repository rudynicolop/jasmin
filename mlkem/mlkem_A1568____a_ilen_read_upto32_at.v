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

(* A1568____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_112 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15827).
Definition offset_114 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15828).
Definition DELTA_76 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15829).
Definition LEN_57 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15830).
Definition TRAIL_33 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15831).
Definition CUR_33 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15832).
Definition AT_77 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15833).
Definition w_79 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15834).
Definition AT32_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15835).
Definition t128_0_17 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15836).
Definition t128_1_25 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15837).

(* Signature *)
Definition tyin_A1568____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1568____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_112.(gv)
    ; offset_114.(gv)
    ; DELTA_76.(gv)
    ; LEN_57.(gv)
    ; TRAIL_33.(gv)
    ; CUR_33.(gv)
    ; AT_77.(gv) ].
Definition tyout_A1568____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1568____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_76.(gv); LEN_57.(gv); TRAIL_33.(gv); AT_77.(gv); w_79.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_77) (Pvar CUR_33)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_33) (Pconst (32)%Z)) (Pvar AT_77))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_57) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_33) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_79.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_7.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_77) (Pvar CUR_33)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_7) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_57)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_79.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_112 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_114) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_76))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_7.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_7) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_76.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_76) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_57.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_57) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_7))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_79.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_76.(gv)
                                                                    ; Lvar LEN_57.(gv)
                                                                    ; Lvar TRAIL_33.(gv)
                                                                    ; Lvar AT32_7.(gv)
                                                                    ; Lvar t128_1_25.(gv) ] A1568____a_ilen_read_upto16_at [:: Pvar buf_112
                                                                    ; Pvar offset_114
                                                                    ; Pvar DELTA_76
                                                                    ; Pvar LEN_57
                                                                    ; Pvar TRAIL_33
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_7 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_79.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_79
                                                                    ; Pvar t128_1_25
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_76.(gv)
                                                                    ; Lvar LEN_57.(gv)
                                                                    ; Lvar TRAIL_33.(gv)
                                                                    ; Lvar AT32_7.(gv)
                                                                    ; Lvar t128_0_17.(gv) ] A1568____a_ilen_read_upto16_at [:: Pvar buf_112
                                                                    ; Pvar offset_114
                                                                    ; Pvar DELTA_76
                                                                    ; Pvar LEN_57
                                                                    ; Pvar TRAIL_33
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_7 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_76.(gv)
                                                                    ; Lvar LEN_57.(gv)
                                                                    ; Lvar TRAIL_33.(gv)
                                                                    ; Lvar AT32_7.(gv)
                                                                    ; Lvar t128_1_25.(gv) ] A1568____a_ilen_read_upto16_at [:: Pvar buf_112
                                                                    ; Pvar offset_114
                                                                    ; Pvar DELTA_76
                                                                    ; Pvar LEN_57
                                                                    ; Pvar TRAIL_33
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_7 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_79.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_25)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_17) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_77.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_33) (Pvar AT32_7))) ]) ].

Definition fd_A1568____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_ilen_read_upto32_at;
    f_params := args_A1568____a_ilen_read_upto32_at;
    f_body := body_A1568____a_ilen_read_upto32_at;
    f_tyout := tyout_A1568____a_ilen_read_upto32_at;
    f_res := res_A1568____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
