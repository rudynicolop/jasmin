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

(* A128____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_84 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16591).
Definition offset_80 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16592).
Definition DELTA_54 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16593).
Definition LEN_43 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16594).
Definition TRAIL_25 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16595).
Definition CUR_25 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16596).
Definition AT_57 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16597).
Definition w_59 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16598).
Definition AT32_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16599).
Definition t128_0_13 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16600).
Definition t128_1_19 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16601).

(* Signature *)
Definition tyin_A128____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 128; aword U64; aint; aint; aint; aint; aint ].
Definition args_A128____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_84.(gv)
    ; offset_80.(gv)
    ; DELTA_54.(gv)
    ; LEN_43.(gv)
    ; TRAIL_25.(gv)
    ; CUR_25.(gv)
    ; AT_57.(gv) ].
Definition tyout_A128____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A128____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_54.(gv); LEN_43.(gv); TRAIL_25.(gv); AT_57.(gv); w_59.(gv) ].

(* Body *)
Definition body_A128____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_57) (Pvar CUR_25)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_25) (Pconst (32)%Z)) (Pvar AT_57))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_43) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_25) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_59.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_5.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_57) (Pvar CUR_25)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_5) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_43)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_59.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_84 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_80) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_54))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_5.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_5) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_54.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_54) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_43.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_43) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_5))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_59.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_54.(gv)
                                                                    ; Lvar LEN_43.(gv)
                                                                    ; Lvar TRAIL_25.(gv)
                                                                    ; Lvar AT32_5.(gv)
                                                                    ; Lvar t128_1_19.(gv) ] A128____a_ilen_read_upto16_at [:: Pvar buf_84
                                                                    ; Pvar offset_80
                                                                    ; Pvar DELTA_54
                                                                    ; Pvar LEN_43
                                                                    ; Pvar TRAIL_25
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_5 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_59.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_59
                                                                    ; Pvar t128_1_19
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_54.(gv)
                                                                    ; Lvar LEN_43.(gv)
                                                                    ; Lvar TRAIL_25.(gv)
                                                                    ; Lvar AT32_5.(gv)
                                                                    ; Lvar t128_0_13.(gv) ] A128____a_ilen_read_upto16_at [:: Pvar buf_84
                                                                    ; Pvar offset_80
                                                                    ; Pvar DELTA_54
                                                                    ; Pvar LEN_43
                                                                    ; Pvar TRAIL_25
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_5 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_54.(gv)
                                                                    ; Lvar LEN_43.(gv)
                                                                    ; Lvar TRAIL_25.(gv)
                                                                    ; Lvar AT32_5.(gv)
                                                                    ; Lvar t128_1_19.(gv) ] A128____a_ilen_read_upto16_at [:: Pvar buf_84
                                                                    ; Pvar offset_80
                                                                    ; Pvar DELTA_54
                                                                    ; Pvar LEN_43
                                                                    ; Pvar TRAIL_25
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_5 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_59.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_19)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_13) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_57.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_25) (Pvar AT32_5))) ]) ].

Definition fd_A128____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____a_ilen_read_upto32_at;
    f_params := args_A128____a_ilen_read_upto32_at;
    f_body := body_A128____a_ilen_read_upto32_at;
    f_tyout := tyout_A128____a_ilen_read_upto32_at;
    f_res := res_A128____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
