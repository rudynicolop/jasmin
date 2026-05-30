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

(* A1184____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_25 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15918).
Definition buf1_25 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15919).
Definition buf2_25 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15920).
Definition buf3_25 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15921).
Definition offset_110 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15922).
Definition _LEN_71 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15923).
Definition st_78 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15924).
Definition i_47 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15925).
Definition x0_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15926).
Definition x1_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15927).
Definition x2_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15928).
Definition x3_9 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15929).
Definition t0_17 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15930).
Definition t1_17 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15931).
Definition t2_15 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15932).
Definition t3_15 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15933).

(* Signature *)
Definition tyin_A1184____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A1184____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_25.(gv)
    ; buf1_25.(gv)
    ; buf2_25.(gv)
    ; buf3_25.(gv)
    ; offset_110.(gv)
    ; _LEN_71.(gv)
    ; st_78.(gv) ].
Definition tyout_A1184____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1184; aarr U8 1184; aarr U8 1184; aarr U8 1184; aword U64 ].
Definition res_A1184____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_25.(gv)
    ; buf1_25.(gv)
    ; buf2_25.(gv)
    ; buf3_25.(gv)
    ; offset_110.(gv) ].

(* Body *)
Definition body_A1184____dumpstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_47.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_47) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_71) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_9.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_9.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_9.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_9.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_47.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_47) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_9.(gv)
                                                                ; Lvar x1_9.(gv)
                                                                ; Lvar x2_9.(gv)
                                                                ; Lvar x3_9.(gv) ] __4u64x4_u256x4 [:: Pvar x0_9
                                                                    ; Pvar x1_9
                                                                    ; Pvar x2_9
                                                                    ; Pvar x3_9 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf0_25.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_110))) AT_none (aword U256) (Pvar x0_9))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf1_25.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_110))) AT_none (aword U256) (Pvar x1_9))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf2_25.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_110))) AT_none (aword U256) (Pvar x2_9))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf3_25.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_110))) AT_none (aword U256) (Pvar x3_9))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_110.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_110) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_47) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_71) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_17.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf0_25.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_110))) AT_none (aword U64) (Pvar t0_17))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_17.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf1_25.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_110))) AT_none (aword U64) (Pvar t1_17))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_15.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf2_25.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_110))) AT_none (aword U64) (Pvar t2_15))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_15.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf3_25.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_110))) AT_none (aword U64) (Pvar t3_15))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_47.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_47) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_110.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_110) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_71) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_17.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_25.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1184____a_ilen_write_upto8 [:: Pvar buf0_25
                                                                    ; Pvar offset_110
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_71) (Pconst (8)%Z)
                                                                    ; Pvar t0_17 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_17.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_25.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1184____a_ilen_write_upto8 [:: Pvar buf1_25
                                                                    ; Pvar offset_110
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_71) (Pconst (8)%Z)
                                                                    ; Pvar t1_17 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_15.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_25.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1184____a_ilen_write_upto8 [:: Pvar buf2_25
                                                                    ; Pvar offset_110
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_71) (Pconst (8)%Z)
                                                                    ; Pvar t2_15 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_15.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_78 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_47)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_25.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1184____a_ilen_write_upto8 [:: Pvar buf3_25
                                                                    ; Pvar offset_110
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_71) (Pconst (8)%Z)
                                                                    ; Pvar t3_15 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_110.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_110) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_71) (Pconst (8)%Z))))) ]
                              [::]) ].

Definition fd_A1184____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____dumpstate_avx2x4;
    f_params := args_A1184____dumpstate_avx2x4;
    f_body := body_A1184____dumpstate_avx2x4;
    f_tyout := tyout_A1184____dumpstate_avx2x4;
    f_res := res_A1184____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
