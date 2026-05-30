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

(* A64____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_72 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16838).
Definition offset_69 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16839).
Definition DELTA_45 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16840).
Definition LEN_36 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16841).
Definition TRAIL_21 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16842).
Definition CUR_21 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16843).
Definition AT_51 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16844).
Definition w_50 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16845).
Definition AT32_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16846).
Definition t128_0_11 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16847).
Definition t128_1_16 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16848).

(* Signature *)
Definition tyin_A64____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 64; aword U64; aint; aint; aint; aint; aint ].
Definition args_A64____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_72.(gv)
    ; offset_69.(gv)
    ; DELTA_45.(gv)
    ; LEN_36.(gv)
    ; TRAIL_21.(gv)
    ; CUR_21.(gv)
    ; AT_51.(gv) ].
Definition tyout_A64____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A64____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_45.(gv); LEN_36.(gv); TRAIL_21.(gv); AT_51.(gv); w_50.(gv) ].

(* Body *)
Definition body_A64____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_51) (Pvar CUR_21)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_21) (Pconst (32)%Z)) (Pvar AT_51))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_36) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_21) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_50.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_4.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_51) (Pvar CUR_21)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_4) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_36)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_50.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_72 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_69) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_45))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_4.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_4) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_45.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_45) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_36.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_36) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_4))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_50.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_45.(gv)
                                                                    ; Lvar LEN_36.(gv)
                                                                    ; Lvar TRAIL_21.(gv)
                                                                    ; Lvar AT32_4.(gv)
                                                                    ; Lvar t128_1_16.(gv) ] A64____a_ilen_read_upto16_at [:: Pvar buf_72
                                                                    ; Pvar offset_69
                                                                    ; Pvar DELTA_45
                                                                    ; Pvar LEN_36
                                                                    ; Pvar TRAIL_21
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_4 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_50.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_50
                                                                    ; Pvar t128_1_16
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_45.(gv)
                                                                    ; Lvar LEN_36.(gv)
                                                                    ; Lvar TRAIL_21.(gv)
                                                                    ; Lvar AT32_4.(gv)
                                                                    ; Lvar t128_0_11.(gv) ] A64____a_ilen_read_upto16_at [:: Pvar buf_72
                                                                    ; Pvar offset_69
                                                                    ; Pvar DELTA_45
                                                                    ; Pvar LEN_36
                                                                    ; Pvar TRAIL_21
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_4 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_45.(gv)
                                                                    ; Lvar LEN_36.(gv)
                                                                    ; Lvar TRAIL_21.(gv)
                                                                    ; Lvar AT32_4.(gv)
                                                                    ; Lvar t128_1_16.(gv) ] A64____a_ilen_read_upto16_at [:: Pvar buf_72
                                                                    ; Pvar offset_69
                                                                    ; Pvar DELTA_45
                                                                    ; Pvar LEN_36
                                                                    ; Pvar TRAIL_21
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_4 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_50.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_16)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_11) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_51.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_21) (Pvar AT32_4))) ]) ].

Definition fd_A64____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_ilen_read_upto32_at;
    f_params := args_A64____a_ilen_read_upto32_at;
    f_body := body_A64____a_ilen_read_upto32_at;
    f_tyout := tyout_A64____a_ilen_read_upto32_at;
    f_res := res_A64____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
