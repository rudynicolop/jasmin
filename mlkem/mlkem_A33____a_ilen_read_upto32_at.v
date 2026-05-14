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

(* A33____a_ilen_read_upto32_at *)
(* Local variables *)
Definition buf_17220 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17220).
Definition offset_17221 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17221).
Definition DELTA_17222 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17222).
Definition LEN_17223 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17223).
Definition TRAIL_17224 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17224).
Definition CUR_17225 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17225).
Definition AT_17226 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17226).
Definition w_17227 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17227).
Definition AT32_17228 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17228).
Definition t128_0_17229 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17229).
Definition t128_1_17230 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17230).

(* Signature *)
Definition tyin_A33____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aint; aint; aint ].
Definition args_A33____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_17220.(gv)
    ; offset_17221.(gv)
    ; DELTA_17222.(gv)
    ; LEN_17223.(gv)
    ; TRAIL_17224.(gv)
    ; CUR_17225.(gv)
    ; AT_17226.(gv) ].
Definition tyout_A33____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A33____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_17222.(gv)
    ; LEN_17223.(gv)
    ; TRAIL_17224.(gv)
    ; AT_17226.(gv)
    ; w_17227.(gv) ].

(* Body *)
Definition body_A33____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_17226) (Pvar CUR_17225)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_17225) (Pconst (32)%Z)) (Pvar AT_17226))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_17223) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_17224) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_17227.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_17228.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17226) (Pvar CUR_17225)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_17228) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_17223)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_17227.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_17220 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17221) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17222))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_17228.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_17228) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_17222.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17222) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_17223.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17223) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_17228))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_17227.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_17222.(gv)
                                                                    ; Lvar LEN_17223.(gv)
                                                                    ; Lvar TRAIL_17224.(gv)
                                                                    ; Lvar AT32_17228.(gv)
                                                                    ; Lvar t128_1_17230.(gv) ] A33____a_ilen_read_upto16_at [:: Pvar buf_17220
                                                                    ; Pvar offset_17221
                                                                    ; Pvar DELTA_17222
                                                                    ; Pvar LEN_17223
                                                                    ; Pvar TRAIL_17224
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_17228 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_17227.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_17227
                                                                    ; Pvar t128_1_17230
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_17222.(gv)
                                                                    ; Lvar LEN_17223.(gv)
                                                                    ; Lvar TRAIL_17224.(gv)
                                                                    ; Lvar AT32_17228.(gv)
                                                                    ; Lvar t128_0_17229.(gv) ] A33____a_ilen_read_upto16_at [:: Pvar buf_17220
                                                                    ; Pvar offset_17221
                                                                    ; Pvar DELTA_17222
                                                                    ; Pvar LEN_17223
                                                                    ; Pvar TRAIL_17224
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_17228 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_17222.(gv)
                                                                    ; Lvar LEN_17223.(gv)
                                                                    ; Lvar TRAIL_17224.(gv)
                                                                    ; Lvar AT32_17228.(gv)
                                                                    ; Lvar t128_1_17230.(gv) ] A33____a_ilen_read_upto16_at [:: Pvar buf_17220
                                                                    ; Pvar offset_17221
                                                                    ; Pvar DELTA_17222
                                                                    ; Pvar LEN_17223
                                                                    ; Pvar TRAIL_17224
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_17228 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_17227.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_17230)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_17229) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_17226.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_17225) (Pvar AT32_17228))) ]) ].

Definition fd_A33____a_ilen_read_upto32_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_ilen_read_upto32_at;
    f_params := args_A33____a_ilen_read_upto32_at;
    f_body := body_A33____a_ilen_read_upto32_at;
    f_tyout := tyout_A33____a_ilen_read_upto32_at;
    f_res := res_A33____a_ilen_read_upto32_at;
    f_extra := tt;
  |}.

End IDO.
