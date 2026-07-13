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

(* A1____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_5 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18075).
Definition buf1_5 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18076).
Definition buf2_5 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18077).
Definition buf3_5 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18078).
Definition offset_14 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18079).
Definition _LEN_17 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18080).
Definition st_24 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18081).
Definition i_15 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18082).
Definition x0_4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18083).
Definition x1_4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18084).
Definition x2_4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18085).
Definition x3_4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18086).
Definition t0_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18087).
Definition t1_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18088).
Definition t2_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18089).
Definition t3_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18090).

(* Signature *)
Definition tyin_A1____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1
    ; aarr U8 1
    ; aarr U8 1
    ; aarr U8 1
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A1____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_5.(gv)
    ; buf1_5.(gv)
    ; buf2_5.(gv)
    ; buf3_5.(gv)
    ; offset_14.(gv)
    ; _LEN_17.(gv)
    ; st_24.(gv) ].
Definition tyout_A1____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1; aarr U8 1; aarr U8 1; aarr U8 1; aword U64 ].
Definition res_A1____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_5.(gv); buf1_5.(gv); buf2_5.(gv); buf3_5.(gv); offset_14.(gv) ].

(* Body *)
Definition body_A1____dumpstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_15.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_4.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_4.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_4.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_4.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_15.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_4.(gv)
                                                                ; Lvar x1_4.(gv)
                                                                ; Lvar x2_4.(gv)
                                                                ; Lvar x3_4.(gv) ] __4u64x4_u256x4 [:: Pvar x0_4
                                                                    ; Pvar x1_4
                                                                    ; Pvar x2_4
                                                                    ; Pvar x3_4 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf0_5.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14))) AT_none (aword U256) (Pvar x0_4))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf1_5.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14))) AT_none (aword U256) (Pvar x1_4))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf2_5.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14))) AT_none (aword U256) (Pvar x2_4))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf3_5.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14))) AT_none (aword U256) (Pvar x3_4))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_14.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_7.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf0_5.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14))) AT_none (aword U64) (Pvar t0_7))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_7.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf1_5.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14))) AT_none (aword U64) (Pvar t1_7))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_5.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf2_5.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14))) AT_none (aword U64) (Pvar t2_5))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_5.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf3_5.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14))) AT_none (aword U64) (Pvar t3_5))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_15.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_14.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_7.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_5.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1____a_ilen_write_upto8 [:: Pvar buf0_5
                                                                    ; Pvar offset_14
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17) (Pconst (8)%Z)
                                                                    ; Pvar t0_7 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_7.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_5.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1____a_ilen_write_upto8 [:: Pvar buf1_5
                                                                    ; Pvar offset_14
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17) (Pconst (8)%Z)
                                                                    ; Pvar t1_7 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_5.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_5.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1____a_ilen_write_upto8 [:: Pvar buf2_5
                                                                    ; Pvar offset_14
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17) (Pconst (8)%Z)
                                                                    ; Pvar t2_5 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_5.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_24 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_5.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1____a_ilen_write_upto8 [:: Pvar buf3_5
                                                                    ; Pvar offset_14
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17) (Pconst (8)%Z)
                                                                    ; Pvar t3_5 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_14.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17) (Pconst (8)%Z))))) ]
                              [::]) ].

Definition fd_A1____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____dumpstate_avx2x4;
    f_params := args_A1____dumpstate_avx2x4;
    f_body := body_A1____dumpstate_avx2x4;
    f_tyout := tyout_A1____dumpstate_avx2x4;
    f_res := res_A1____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
