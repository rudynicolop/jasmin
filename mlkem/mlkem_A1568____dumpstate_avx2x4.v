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

(* A1568____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_29 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15536).
Definition buf1_29 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15537).
Definition buf2_29 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15538).
Definition buf3_29 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15539).
Definition offset_127 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15540).
Definition _LEN_81 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15541).
Definition st_88 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15542).
Definition i_53 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15543).
Definition x0_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15544).
Definition x1_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15545).
Definition x2_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15546).
Definition x3_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15547).
Definition t0_19 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15548).
Definition t1_19 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15549).
Definition t2_17 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15550).
Definition t3_17 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15551).

(* Signature *)
Definition tyin_A1568____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A1568____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_29.(gv)
    ; buf1_29.(gv)
    ; buf2_29.(gv)
    ; buf3_29.(gv)
    ; offset_127.(gv)
    ; _LEN_81.(gv)
    ; st_88.(gv) ].
Definition tyout_A1568____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1568; aarr U8 1568; aarr U8 1568; aarr U8 1568; aword U64 ].
Definition res_A1568____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_29.(gv)
    ; buf1_29.(gv)
    ; buf2_29.(gv)
    ; buf3_29.(gv)
    ; offset_127.(gv) ].

(* Body *)
Definition body_A1568____dumpstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_53.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_53) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_81) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_10.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_10.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_10.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_10.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_53.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_53) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_10.(gv)
                                                                ; Lvar x1_10.(gv)
                                                                ; Lvar x2_10.(gv)
                                                                ; Lvar x3_10.(gv) ] __4u64x4_u256x4 [:: Pvar x0_10
                                                                    ; Pvar x1_10
                                                                    ; Pvar x2_10
                                                                    ; Pvar x3_10 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf0_29.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_127))) AT_none (aword U256) (Pvar x0_10))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf1_29.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_127))) AT_none (aword U256) (Pvar x1_10))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf2_29.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_127))) AT_none (aword U256) (Pvar x2_10))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf3_29.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_127))) AT_none (aword U256) (Pvar x3_10))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_127.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_127) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_53) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_81) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_19.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf0_29.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_127))) AT_none (aword U64) (Pvar t0_19))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_19.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf1_29.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_127))) AT_none (aword U64) (Pvar t1_19))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_17.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf2_29.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_127))) AT_none (aword U64) (Pvar t2_17))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_17.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf3_29.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_127))) AT_none (aword U64) (Pvar t3_17))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_53.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_53) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_127.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_127) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_81) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_19.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_29.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1568____a_ilen_write_upto8 [:: Pvar buf0_29
                                                                    ; Pvar offset_127
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_81) (Pconst (8)%Z)
                                                                    ; Pvar t0_19 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_19.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_29.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1568____a_ilen_write_upto8 [:: Pvar buf1_29
                                                                    ; Pvar offset_127
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_81) (Pconst (8)%Z)
                                                                    ; Pvar t1_19 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_17.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_29.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1568____a_ilen_write_upto8 [:: Pvar buf2_29
                                                                    ; Pvar offset_127
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_81) (Pconst (8)%Z)
                                                                    ; Pvar t2_17 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_17.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_88 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_53)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_29.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A1568____a_ilen_write_upto8 [:: Pvar buf3_29
                                                                    ; Pvar offset_127
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_81) (Pconst (8)%Z)
                                                                    ; Pvar t3_17 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_127.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_127) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_81) (Pconst (8)%Z))))) ]
                              [::]) ].

Definition fd_A1568____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____dumpstate_avx2x4;
    f_params := args_A1568____dumpstate_avx2x4;
    f_body := body_A1568____dumpstate_avx2x4;
    f_tyout := tyout_A1568____dumpstate_avx2x4;
    f_res := res_A1568____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
