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

(* A1120____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_33 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15154).
Definition buf1_33 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15155).
Definition buf2_33 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15156).
Definition buf3_33 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15157).
Definition offset_144 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15158).
Definition _LEN_91 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15159).
Definition st_98 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15160).
Definition i_59 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15161).
Definition x0_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15162).
Definition x1_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15163).
Definition x2_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15164).
Definition x3_11 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15165).
Definition t0_21 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15166).
Definition t1_21 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15167).
Definition t2_19 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15168).
Definition t3_19 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15169).

(* Signature *)
Definition tyin_A1120____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A1120____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_33.(gv)
    ; buf1_33.(gv)
    ; buf2_33.(gv)
    ; buf3_33.(gv)
    ; offset_144.(gv)
    ; _LEN_91.(gv)
    ; st_98.(gv) ].
Definition tyout_A1120____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1120; aarr U8 1120; aarr U8 1120; aarr U8 1120; aword U64 ].
Definition res_A1120____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_33.(gv)
    ; buf1_33.(gv)
    ; buf2_33.(gv)
    ; buf3_33.(gv)
    ; offset_144.(gv) ].

(* Body *)
Definition body_A1120____dumpstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_59.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_59) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_91) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_11.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_11.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_11.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_11.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_59.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_59) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_11.(gv)
                                                                ; Lvar x1_11.(gv)
                                                                ; Lvar x2_11.(gv)
                                                                ; Lvar x3_11.(gv) ] __4u64x4_u256x4 [:: Pvar x0_11
                                                                    ; Pvar x1_11
                                                                    ; Pvar x2_11
                                                                    ; Pvar x3_11 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf0_33.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_144))) AT_none (aword U256) (Pvar x0_11))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf1_33.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_144))) AT_none (aword U256) (Pvar x1_11))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf2_33.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_144))) AT_none (aword U256) (Pvar x2_11))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf3_33.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_144))) AT_none (aword U256) (Pvar x3_11))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_144.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_144) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_59) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_91) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_21.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf0_33.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_144))) AT_none (aword U64) (Pvar t0_21))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_21.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf1_33.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_144))) AT_none (aword U64) (Pvar t1_21))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_19.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf2_33.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_144))) AT_none (aword U64) (Pvar t2_19))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_19.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf3_33.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_144))) AT_none (aword U64) (Pvar t3_19))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_59.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_59) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_144.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_144) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_91) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_21.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_33.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1120____a_ilen_write_upto8 [:: Pvar buf0_33
                                                                    ; Pvar offset_144
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_91) (Pconst (8)%Z)
                                                                    ; Pvar t0_21 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_21.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_33.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1120____a_ilen_write_upto8 [:: Pvar buf1_33
                                                                    ; Pvar offset_144
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_91) (Pconst (8)%Z)
                                                                    ; Pvar t1_21 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_19.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_33.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1120____a_ilen_write_upto8 [:: Pvar buf2_33
                                                                    ; Pvar offset_144
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_91) (Pconst (8)%Z)
                                                                    ; Pvar t2_19 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_19.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_98 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_59)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_33.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1120____a_ilen_write_upto8 [:: Pvar buf3_33
                                                                    ; Pvar offset_144
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_91) (Pconst (8)%Z)
                                                                    ; Pvar t3_19 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_144.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_144) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_91) (Pconst (8)%Z))))) ]
                              [::]) ].

Definition fd_A1120____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____dumpstate_avx2x4;
    f_params := args_A1120____dumpstate_avx2x4;
    f_body := body_A1120____dumpstate_avx2x4;
    f_tyout := tyout_A1120____dumpstate_avx2x4;
    f_res := res_A1120____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
