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

(* A2____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_9 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17693).
Definition buf1_9 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17694).
Definition buf2_9 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17695).
Definition buf3_9 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17696).
Definition offset_31 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17697).
Definition _LEN_27 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17698).
Definition st_34 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17699).
Definition i_21 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17700).
Definition x0_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17701).
Definition x1_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17702).
Definition x2_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17703).
Definition x3_5 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17704).
Definition t0_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17705).
Definition t1_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17706).
Definition t2_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17707).
Definition t3_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17708).

(* Signature *)
Definition tyin_A2____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 2
    ; aarr U8 2
    ; aarr U8 2
    ; aarr U8 2
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A2____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_9.(gv)
    ; buf1_9.(gv)
    ; buf2_9.(gv)
    ; buf3_9.(gv)
    ; offset_31.(gv)
    ; _LEN_27.(gv)
    ; st_34.(gv) ].
Definition tyout_A2____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 2; aarr U8 2; aarr U8 2; aarr U8 2; aword U64 ].
Definition res_A2____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_9.(gv); buf1_9.(gv); buf2_9.(gv); buf3_9.(gv); offset_31.(gv) ].

(* Body *)
Definition body_A2____dumpstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_21.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_21) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_27) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_5.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_5.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_5.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_5.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_21.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_21) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_5.(gv)
                                                                ; Lvar x1_5.(gv)
                                                                ; Lvar x2_5.(gv)
                                                                ; Lvar x3_5.(gv) ] __4u64x4_u256x4 [:: Pvar x0_5
                                                                    ; Pvar x1_5
                                                                    ; Pvar x2_5
                                                                    ; Pvar x3_5 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf0_9.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_31))) AT_none (aword U256) (Pvar x0_5))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf1_9.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_31))) AT_none (aword U256) (Pvar x1_5))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf2_9.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_31))) AT_none (aword U256) (Pvar x2_5))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf3_9.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_31))) AT_none (aword U256) (Pvar x3_5))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_31.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_31) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_21) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_27) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_9.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf0_9.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_31))) AT_none (aword U64) (Pvar t0_9))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_9.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf1_9.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_31))) AT_none (aword U64) (Pvar t1_9))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_7.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf2_9.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_31))) AT_none (aword U64) (Pvar t2_7))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_7.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf3_9.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_31))) AT_none (aword U64) (Pvar t3_7))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_21.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_21) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_31.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_31) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_27) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_9.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_9.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A2____a_ilen_write_upto8 [:: Pvar buf0_9
                                                                    ; Pvar offset_31
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_27) (Pconst (8)%Z)
                                                                    ; Pvar t0_9 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_9.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_9.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A2____a_ilen_write_upto8 [:: Pvar buf1_9
                                                                    ; Pvar offset_31
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_27) (Pconst (8)%Z)
                                                                    ; Pvar t1_9 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_7.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_9.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A2____a_ilen_write_upto8 [:: Pvar buf2_9
                                                                    ; Pvar offset_31
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_27) (Pconst (8)%Z)
                                                                    ; Pvar t2_7 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_7.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_34 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_21)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_9.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A2____a_ilen_write_upto8 [:: Pvar buf3_9
                                                                    ; Pvar offset_31
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_27) (Pconst (8)%Z)
                                                                    ; Pvar t3_7 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_31.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_31) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_27) (Pconst (8)%Z))))) ]
                              [::]) ].

Definition fd_A2____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____dumpstate_avx2x4;
    f_params := args_A2____dumpstate_avx2x4;
    f_body := body_A2____dumpstate_avx2x4;
    f_tyout := tyout_A2____dumpstate_avx2x4;
    f_res := res_A2____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
