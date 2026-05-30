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

(* A128____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_21 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16300).
Definition buf1_21 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16301).
Definition buf2_21 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16302).
Definition buf3_21 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16303).
Definition offset_93 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16304).
Definition _LEN_61 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16305).
Definition st_68 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 16306).
Definition i_41 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16307).
Definition x0_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16308).
Definition x1_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16309).
Definition x2_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16310).
Definition x3_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16311).
Definition t0_15 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16312).
Definition t1_15 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16313).
Definition t2_13 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16314).
Definition t3_13 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16315).

(* Signature *)
Definition tyin_A128____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A128____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_21.(gv)
    ; buf1_21.(gv)
    ; buf2_21.(gv)
    ; buf3_21.(gv)
    ; offset_93.(gv)
    ; _LEN_61.(gv)
    ; st_68.(gv) ].
Definition tyout_A128____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 128; aarr U8 128; aarr U8 128; aarr U8 128; aword U64 ].
Definition res_A128____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_21.(gv)
    ; buf1_21.(gv)
    ; buf2_21.(gv)
    ; buf3_21.(gv)
    ; offset_93.(gv) ].

(* Body *)
Definition body_A128____dumpstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_41.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_41) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_61) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_8.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_8.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_8.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_8.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_41.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_41) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_8.(gv)
                                                                ; Lvar x1_8.(gv)
                                                                ; Lvar x2_8.(gv)
                                                                ; Lvar x3_8.(gv) ] __4u64x4_u256x4 [:: Pvar x0_8
                                                                    ; Pvar x1_8
                                                                    ; Pvar x2_8
                                                                    ; Pvar x3_8 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf0_21.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_93))) AT_none (aword U256) (Pvar x0_8))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf1_21.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_93))) AT_none (aword U256) (Pvar x1_8))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf2_21.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_93))) AT_none (aword U256) (Pvar x2_8))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf3_21.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_93))) AT_none (aword U256) (Pvar x3_8))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_93.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_93) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_41) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_61) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_15.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf0_21.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_93))) AT_none (aword U64) (Pvar t0_15))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_15.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf1_21.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_93))) AT_none (aword U64) (Pvar t1_15))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_13.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf2_21.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_93))) AT_none (aword U64) (Pvar t2_13))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_13.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf3_21.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_93))) AT_none (aword U64) (Pvar t3_13))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_41.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_41) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_93.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_93) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_61) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_15.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_21.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A128____a_ilen_write_upto8 [:: Pvar buf0_21
                                                                    ; Pvar offset_93
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_61) (Pconst (8)%Z)
                                                                    ; Pvar t0_15 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_15.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_21.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A128____a_ilen_write_upto8 [:: Pvar buf1_21
                                                                    ; Pvar offset_93
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_61) (Pconst (8)%Z)
                                                                    ; Pvar t1_15 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_13.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_21.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A128____a_ilen_write_upto8 [:: Pvar buf2_21
                                                                    ; Pvar offset_93
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_61) (Pconst (8)%Z)
                                                                    ; Pvar t2_13 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_13.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_41)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_21.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A128____a_ilen_write_upto8 [:: Pvar buf3_21
                                                                    ; Pvar offset_93
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_61) (Pconst (8)%Z)
                                                                    ; Pvar t3_13 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_93.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_93) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_61) (Pconst (8)%Z))))) ]
                              [::]) ].

Definition fd_A128____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____dumpstate_avx2x4;
    f_params := args_A128____dumpstate_avx2x4;
    f_body := body_A128____dumpstate_avx2x4;
    f_tyout := tyout_A128____dumpstate_avx2x4;
    f_res := res_A128____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
