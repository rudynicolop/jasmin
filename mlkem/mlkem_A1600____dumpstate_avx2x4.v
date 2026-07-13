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

(* A1600____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_37 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14772).
Definition buf1_37 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14773).
Definition buf2_37 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14774).
Definition buf3_37 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14775).
Definition offset_161 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14776).
Definition _LEN_101 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14777).
Definition st_108 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14778).
Definition i_65 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14779).
Definition x0_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14780).
Definition x1_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14781).
Definition x2_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14782).
Definition x3_12 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14783).
Definition t0_23 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14784).
Definition t1_23 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14785).
Definition t2_21 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14786).
Definition t3_21 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14787).

(* Signature *)
Definition tyin_A1600____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A1600____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_37.(gv)
    ; buf1_37.(gv)
    ; buf2_37.(gv)
    ; buf3_37.(gv)
    ; offset_161.(gv)
    ; _LEN_101.(gv)
    ; st_108.(gv) ].
Definition tyout_A1600____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1600; aarr U8 1600; aarr U8 1600; aarr U8 1600; aword U64 ].
Definition res_A1600____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_37.(gv)
    ; buf1_37.(gv)
    ; buf2_37.(gv)
    ; buf3_37.(gv)
    ; offset_161.(gv) ].

(* Body *)
Definition body_A1600____dumpstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_65.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_65) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_101) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_12.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_12.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_12.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_12.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_65.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_65) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_12.(gv)
                                                                ; Lvar x1_12.(gv)
                                                                ; Lvar x2_12.(gv)
                                                                ; Lvar x3_12.(gv) ] __4u64x4_u256x4 [:: Pvar x0_12
                                                                    ; Pvar x1_12
                                                                    ; Pvar x2_12
                                                                    ; Pvar x3_12 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf0_37.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_161))) AT_none (aword U256) (Pvar x0_12))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf1_37.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_161))) AT_none (aword U256) (Pvar x1_12))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf2_37.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_161))) AT_none (aword U256) (Pvar x2_12))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf3_37.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_161))) AT_none (aword U256) (Pvar x3_12))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_161.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_161) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_65) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_101) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_23.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf0_37.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_161))) AT_none (aword U64) (Pvar t0_23))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_23.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf1_37.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_161))) AT_none (aword U64) (Pvar t1_23))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_21.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf2_37.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_161))) AT_none (aword U64) (Pvar t2_21))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_21.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf3_37.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_161))) AT_none (aword U64) (Pvar t3_21))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_65.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_65) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_161.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_161) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_101) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_23.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_37.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1600____a_ilen_write_upto8 [:: Pvar buf0_37
                                                                    ; Pvar offset_161
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_101) (Pconst (8)%Z)
                                                                    ; Pvar t0_23 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_23.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_37.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1600____a_ilen_write_upto8 [:: Pvar buf1_37
                                                                    ; Pvar offset_161
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_101) (Pconst (8)%Z)
                                                                    ; Pvar t1_23 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_21.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_37.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1600____a_ilen_write_upto8 [:: Pvar buf2_37
                                                                    ; Pvar offset_161
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_101) (Pconst (8)%Z)
                                                                    ; Pvar t2_21 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_21.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_108 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_65)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_37.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1600____a_ilen_write_upto8 [:: Pvar buf3_37
                                                                    ; Pvar offset_161
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_101) (Pconst (8)%Z)
                                                                    ; Pvar t3_21 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_161.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_161) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_101) (Pconst (8)%Z))))) ]
                              [::]) ].

Definition fd_A1600____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____dumpstate_avx2x4;
    f_params := args_A1600____dumpstate_avx2x4;
    f_body := body_A1600____dumpstate_avx2x4;
    f_tyout := tyout_A1600____dumpstate_avx2x4;
    f_res := res_A1600____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
