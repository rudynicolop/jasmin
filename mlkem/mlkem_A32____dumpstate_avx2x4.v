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

(* A32____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_13 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17311).
Definition buf1_13 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17312).
Definition buf2_13 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17313).
Definition buf3_13 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17314).
Definition offset_48 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17315).
Definition _LEN_37 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17316).
Definition st_44 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17317).
Definition i_27 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17318).
Definition x0_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17319).
Definition x1_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17320).
Definition x2_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17321).
Definition x3_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17322).
Definition t0_11 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17323).
Definition t1_11 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17324).
Definition t2_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17325).
Definition t3_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17326).

(* Signature *)
Definition tyin_A32____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 32
    ; aarr U8 32
    ; aarr U8 32
    ; aarr U8 32
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A32____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_13.(gv)
    ; buf1_13.(gv)
    ; buf2_13.(gv)
    ; buf3_13.(gv)
    ; offset_48.(gv)
    ; _LEN_37.(gv)
    ; st_44.(gv) ].
Definition tyout_A32____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 32; aarr U8 32; aarr U8 32; aarr U8 32; aword U64 ].
Definition res_A32____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_13.(gv)
    ; buf1_13.(gv)
    ; buf2_13.(gv)
    ; buf3_13.(gv)
    ; offset_48.(gv) ].

(* Body *)
Definition body_A32____dumpstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_27.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_27) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_37) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_6.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_6.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_6.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_6.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_27.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_27) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_6.(gv)
                                                                ; Lvar x1_6.(gv)
                                                                ; Lvar x2_6.(gv)
                                                                ; Lvar x3_6.(gv) ] __4u64x4_u256x4 [:: Pvar x0_6
                                                                    ; Pvar x1_6
                                                                    ; Pvar x2_6
                                                                    ; Pvar x3_6 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf0_13.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_48))) AT_none (aword U256) (Pvar x0_6))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf1_13.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_48))) AT_none (aword U256) (Pvar x1_6))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf2_13.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_48))) AT_none (aword U256) (Pvar x2_6))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf3_13.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_48))) AT_none (aword U256) (Pvar x3_6))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_48.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_48) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_27) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_37) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_11.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf0_13.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_48))) AT_none (aword U64) (Pvar t0_11))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_11.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf1_13.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_48))) AT_none (aword U64) (Pvar t1_11))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_9.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf2_13.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_48))) AT_none (aword U64) (Pvar t2_9))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_9.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf3_13.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_48))) AT_none (aword U64) (Pvar t3_9))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_27.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_27) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_48.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_48) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_37) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_11.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_13.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A32____a_ilen_write_upto8 [:: Pvar buf0_13
                                                                    ; Pvar offset_48
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_37) (Pconst (8)%Z)
                                                                    ; Pvar t0_11 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_11.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_13.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A32____a_ilen_write_upto8 [:: Pvar buf1_13
                                                                    ; Pvar offset_48
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_37) (Pconst (8)%Z)
                                                                    ; Pvar t1_11 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_9.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_13.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A32____a_ilen_write_upto8 [:: Pvar buf2_13
                                                                    ; Pvar offset_48
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_37) (Pconst (8)%Z)
                                                                    ; Pvar t2_9 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_9.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_44 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_27)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_13.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A32____a_ilen_write_upto8 [:: Pvar buf3_13
                                                                    ; Pvar offset_48
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_37) (Pconst (8)%Z)
                                                                    ; Pvar t3_9 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_48.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_48) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_37) (Pconst (8)%Z))))) ]
                              [::]) ].

Definition fd_A32____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____dumpstate_avx2x4;
    f_params := args_A32____dumpstate_avx2x4;
    f_body := body_A32____dumpstate_avx2x4;
    f_tyout := tyout_A32____dumpstate_avx2x4;
    f_res := res_A32____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
