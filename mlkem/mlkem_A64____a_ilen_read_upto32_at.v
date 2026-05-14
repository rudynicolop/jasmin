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
Definition buf_16838 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 16838).
Definition offset_16839 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16839).
Definition DELTA_16840 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16840).
Definition LEN_16841 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16841).
Definition TRAIL_16842 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16842).
Definition CUR_16843 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16843).
Definition AT_16844 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16844).
Definition w_16845 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16845).
Definition AT32_16846 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16846).
Definition t128_0_16847 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16847).
Definition t128_1_16848 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16848).

(* Signature *)
Definition tyin_A64____a_ilen_read_upto32_at : seq atype :=
  [:: aarr U8 64; aword U64; aint; aint; aint; aint; aint ].
Definition args_A64____a_ilen_read_upto32_at : seq var_i :=
  [:: buf_16838.(gv)
    ; offset_16839.(gv)
    ; DELTA_16840.(gv)
    ; LEN_16841.(gv)
    ; TRAIL_16842.(gv)
    ; CUR_16843.(gv)
    ; AT_16844.(gv) ].
Definition tyout_A64____a_ilen_read_upto32_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A64____a_ilen_read_upto32_at : seq var_i :=
  [:: DELTA_16840.(gv)
    ; LEN_16841.(gv)
    ; TRAIL_16842.(gv)
    ; AT_16844.(gv)
    ; w_16845.(gv) ].

(* Body *)
Definition body_A64____a_ilen_read_upto32_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_16844) (Pvar CUR_16843)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_16843) (Pconst (32)%Z)) (Pvar AT_16844))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_16841) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_16842) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_16845.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT32_16846.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_16844) (Pvar CUR_16843)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar AT32_16846) (Pconst (0)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_16841)))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_16845.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 buf_16838 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16839) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16840))))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT32_16846.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT32_16846) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_16840.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16840) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_16841.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16841) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar AT32_16846))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_16845.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_16840.(gv)
                                                                    ; Lvar LEN_16841.(gv)
                                                                    ; Lvar TRAIL_16842.(gv)
                                                                    ; Lvar AT32_16846.(gv)
                                                                    ; Lvar t128_1_16848.(gv) ] A64____a_ilen_read_upto16_at [:: Pvar buf_16838
                                                                    ; Pvar offset_16839
                                                                    ; Pvar DELTA_16840
                                                                    ; Pvar LEN_16841
                                                                    ; Pvar TRAIL_16842
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_16846 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_16845.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar w_16845
                                                                    ; Pvar t128_1_16848
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_16840.(gv)
                                                                    ; Lvar LEN_16841.(gv)
                                                                    ; Lvar TRAIL_16842.(gv)
                                                                    ; Lvar AT32_16846.(gv)
                                                                    ; Lvar t128_0_16847.(gv) ] A64____a_ilen_read_upto16_at [:: Pvar buf_16838
                                                                    ; Pvar offset_16839
                                                                    ; Pvar DELTA_16840
                                                                    ; Pvar LEN_16841
                                                                    ; Pvar TRAIL_16842
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT32_16846 ])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_16840.(gv)
                                                                    ; Lvar LEN_16841.(gv)
                                                                    ; Lvar TRAIL_16842.(gv)
                                                                    ; Lvar AT32_16846.(gv)
                                                                    ; Lvar t128_1_16848.(gv) ] A64____a_ilen_read_upto16_at [:: Pvar buf_16838
                                                                    ; Pvar offset_16839
                                                                    ; Pvar DELTA_16840
                                                                    ; Pvar LEN_16841
                                                                    ; Pvar TRAIL_16842
                                                                    ; Pconst (16)%Z
                                                                    ; Pvar AT32_16846 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_16845.(gv)) AT_none (aword U256) (PappN (Opack U256 PE128) [:: Papp1 (Oint_of_word Unsigned U128) (Pvar t128_1_16848)
                                                                    ; Papp1 (Oint_of_word Unsigned U128) (Pvar t128_0_16847) ])) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_16844.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_16843) (Pvar AT32_16846))) ]) ].

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
