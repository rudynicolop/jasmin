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

(* _gen_matrix_buf_rejection *)
(* Local variables *)
Definition pol_2 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13787).
Definition counter_1 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13788).
Definition buf_174 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 13789).
Definition buf_offset_1 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13790).
Definition ms_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13791).
Definition load_shuffle_1 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13792).
Definition mask_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13793).
Definition bounds_1 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13794).
Definition ones_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13795).
Definition sst_1 : gvar := mk_rocq_gvar Slocal (aarr U8 2048) (mkident 13796).
Definition saved_buf_offset : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13797).
Definition condition_loop : gvar :=
  mk_rocq_gvar Slocal (abool) (mkident 13798).

(* Signature *)
Definition tyin__gen_matrix_buf_rejection : seq atype :=
  [:: aarr U16 256; aword U64; aarr U8 536; aword U64 ].
Definition args__gen_matrix_buf_rejection : seq var_i :=
  [:: pol_2.(gv); counter_1.(gv); buf_174.(gv); buf_offset_1.(gv) ].
Definition tyout__gen_matrix_buf_rejection : seq atype :=
  [:: aarr U16 256; aword U64 ].
Definition res__gen_matrix_buf_rejection : seq var_i :=
  [:: pol_2.(gv); counter_1.(gv) ].

(* Body *)
Definition body__gen_matrix_buf_rejection : cmd :=
  [:: MkI dummy_instr_info (Copn [:: Lvar ms_2.(gv) ] AT_none (Oslh (SLHinit)) [::])
    ; MkI dummy_instr_info (Cassgn (Lvar load_shuffle_1.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 sample_load_shuffle (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar mask_6.(gv)) AT_none (aword U256) (Pvar sample_mask))
    ; MkI dummy_instr_info (Cassgn (Lvar bounds_1.(gv)) AT_none (aword U256) (Pvar sample_q))
    ; MkI dummy_instr_info (Cassgn (Lvar ones_1.(gv)) AT_none (aword U256) (Pvar sample_ones))
    ; MkI dummy_instr_info (Cassgn (Lvar sst_1.(gv)) AT_none (aarr U8 2048) (Pvar sample_shuffle_table))
    ; MkI dummy_instr_info (Cassgn (Lvar saved_buf_offset.(gv)) AT_none (aword U64) (Pvar buf_offset_1))
    ; MkI dummy_instr_info (Cassgn (Lvar buf_offset_1.(gv)) AT_none (aword U64) (Pvar buf_offset_1))
    ; MkI dummy_instr_info (Cwhile Align
                              [:: MkI dummy_instr_info (Cassgn (Lvar condition_loop.(gv)) AT_none (abool) (Papp2 (Olt (Cmp_w Unsigned U64)) (Pvar buf_offset_1) (Papp1 (Oword_of_int U64) (Papp2 (Oadd (Op_int)) (Papp2 (Osub (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (168)%Z)) (Pconst (48)%Z)) (Pconst (1)%Z))))) ]
                              (Pvar condition_loop)
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar ms_2.(gv) ] AT_none (Oslh (SLHupdate)) [:: Pvar condition_loop
                                                                    ; Pvar ms_2 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar condition_loop.(gv)) AT_none (abool) (Papp2 (Olt (Cmp_w Unsigned U64)) (Pvar counter_1) (Papp1 (Oword_of_int U64) (Papp2 (Oadd (Op_int)) (Papp2 (Osub (Op_int)) (Pconst (256)%Z) (Pconst (32)%Z)) (Pconst (1)%Z)))))
                                ; MkI dummy_instr_info (Cif
                                                          (Pvar condition_loop)
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar ms_2.(gv) ] AT_none (Oslh (SLHupdate)) [:: Pvar condition_loop
                                                                    ; Pvar ms_2 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar pol_2.(gv)
                                                                  ; Lvar counter_1.(gv) ] __gen_matrix_buf_rejection_filter48 [:: Pvar pol_2
                                                                    ; Pvar counter_1
                                                                    ; Pvar buf_174
                                                                    ; Pvar buf_offset_1
                                                                    ; Pvar load_shuffle_1
                                                                    ; Pvar mask_6
                                                                    ; Pvar bounds_1
                                                                    ; Pvar sst_1
                                                                    ; Pvar ones_1
                                                                    ; Pvar ms_2 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar saved_buf_offset.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar saved_buf_offset) (Papp1 (Oword_of_int U64) (Pconst (48)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_offset_1.(gv)) AT_none (aword U64) (Pvar saved_buf_offset))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar buf_offset_1.(gv) ] AT_none (Oslh (SLHprotect U64)) [:: Pvar buf_offset_1
                                                                    ; Pvar ms_2 ]) ]
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar ms_2.(gv) ] AT_none (Oslh (SLHupdate)) [:: Papp1 (Onot) (Pvar condition_loop)
                                                                    ; Pvar ms_2 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_offset_1.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (168)%Z)))) ]) ])
    ; MkI dummy_instr_info (Copn [:: Lvar ms_2.(gv) ] AT_none (Oslh (SLHupdate)) [:: Papp1 (Onot) (Pvar condition_loop)
                                                                    ; Pvar ms_2 ])
    ; MkI dummy_instr_info (Cassgn (Lvar buf_offset_1.(gv)) AT_none (aword U64) (Pvar saved_buf_offset))
    ; MkI dummy_instr_info (Copn [:: Lvar buf_offset_1.(gv) ] AT_none (Oslh (SLHprotect U64)) [:: Pvar buf_offset_1
                                                                    ; Pvar ms_2 ])
    ; MkI dummy_instr_info (Cwhile Align
                              [:: MkI dummy_instr_info (Cassgn (Lvar condition_loop.(gv)) AT_none (abool) (Papp2 (Olt (Cmp_w Unsigned U64)) (Pvar buf_offset_1) (Papp1 (Oword_of_int U64) (Papp2 (Oadd (Op_int)) (Papp2 (Osub (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (168)%Z)) (Pconst (24)%Z)) (Pconst (1)%Z))))) ]
                              (Pvar condition_loop)
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar ms_2.(gv) ] AT_none (Oslh (SLHupdate)) [:: Pvar condition_loop
                                                                    ; Pvar ms_2 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar condition_loop.(gv)) AT_none (abool) (Papp2 (Olt (Cmp_w Unsigned U64)) (Pvar counter_1) (Papp1 (Oword_of_int U64) (Pconst (256)%Z))))
                                ; MkI dummy_instr_info (Cif
                                                          (Pvar condition_loop)
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar ms_2.(gv) ] AT_none (Oslh (SLHupdate)) [:: Pvar condition_loop
                                                                    ; Pvar ms_2 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [::] AT_none (Opseudo_op (Ospill Spill [:: aword U64 ])) [:: Pvar buf_offset_1 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar pol_2.(gv)
                                                                  ; Lvar counter_1.(gv)
                                                                  ; Lvar ms_2.(gv) ] __gen_matrix_buf_rejection_filter24 [:: Pvar pol_2
                                                                    ; Pvar counter_1
                                                                    ; Pvar buf_174
                                                                    ; Pvar buf_offset_1
                                                                    ; Pvar load_shuffle_1
                                                                    ; Pvar mask_6
                                                                    ; Pvar bounds_1
                                                                    ; Pvar sst_1
                                                                    ; Pvar ones_1
                                                                    ; Pvar ms_2 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aword U64 ])) [:: Pvar buf_offset_1 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar buf_offset_1.(gv) ] AT_none (Oslh (SLHprotect U64)) [:: Pvar buf_offset_1
                                                                    ; Pvar ms_2 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_offset_1.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar buf_offset_1) (Papp1 (Oword_of_int U64) (Pconst (24)%Z)))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar ms_2.(gv) ] AT_none (Oslh (SLHupdate)) [:: Papp1 (Onot) (Pvar condition_loop)
                                                                    ; Pvar ms_2 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar buf_offset_1.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (168)%Z)))) ]) ]) ].

Definition fd__gen_matrix_buf_rejection : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__gen_matrix_buf_rejection;
    f_params := args__gen_matrix_buf_rejection;
    f_body := body__gen_matrix_buf_rejection;
    f_tyout := tyout__gen_matrix_buf_rejection;
    f_res := res__gen_matrix_buf_rejection;
    f_extra := tt;
  |}.

End IDO.
