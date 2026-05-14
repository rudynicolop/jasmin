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

(* ABUFLEN____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_14390 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14390).
Definition buf1_14391 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14391).
Definition buf2_14392 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14392).
Definition buf3_14393 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14393).
Definition offset_14394 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14394).
Definition _LEN_14395 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14395).
Definition st_14396 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14396).
Definition i_14397 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14397).
Definition x0_14398 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14398).
Definition x1_14399 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14399).
Definition x2_14400 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14400).
Definition x3_14401 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14401).
Definition t0_14402 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14402).
Definition t1_14403 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14403).
Definition t2_14404 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14404).
Definition t3_14405 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14405).

(* Signature *)
Definition tyin_ABUFLEN____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_ABUFLEN____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_14390.(gv)
    ; buf1_14391.(gv)
    ; buf2_14392.(gv)
    ; buf3_14393.(gv)
    ; offset_14394.(gv)
    ; _LEN_14395.(gv)
    ; st_14396.(gv) ].
Definition tyout_ABUFLEN____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 536; aarr U8 536; aarr U8 536; aarr U8 536; aword U64 ].
Definition res_ABUFLEN____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_14390.(gv)
    ; buf1_14391.(gv)
    ; buf2_14392.(gv)
    ; buf3_14393.(gv)
    ; offset_14394.(gv) ].

(* Body *)
Definition body_ABUFLEN____dumpstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_14397.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14397) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14395) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_14398.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_14399.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_14400.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_14401.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_14397.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14397) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_14398.(gv)
                                                                ; Lvar x1_14399.(gv)
                                                                ; Lvar x2_14400.(gv)
                                                                ; Lvar x3_14401.(gv) ] __4u64x4_u256x4 [:: Pvar x0_14398
                                                                    ; Pvar x1_14399
                                                                    ; Pvar x2_14400
                                                                    ; Pvar x3_14401 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf0_14390.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14394))) AT_none (aword U256) (Pvar x0_14398))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf1_14391.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14394))) AT_none (aword U256) (Pvar x1_14399))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf2_14392.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14394))) AT_none (aword U256) (Pvar x2_14400))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf3_14393.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14394))) AT_none (aword U256) (Pvar x3_14401))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_14394.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14394) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14397) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14395) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_14402.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf0_14390.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14394))) AT_none (aword U64) (Pvar t0_14402))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_14403.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf1_14391.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14394))) AT_none (aword U64) (Pvar t1_14403))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_14404.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf2_14392.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14394))) AT_none (aword U64) (Pvar t2_14404))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_14405.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf3_14393.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14394))) AT_none (aword U64) (Pvar t3_14405))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_14397.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14397) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_14394.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14394) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14395) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_14402.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_14390.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf0_14390
                                                                    ; Pvar offset_14394
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14395) (Pconst (8)%Z)
                                                                    ; Pvar t0_14402 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_14403.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_14391.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf1_14391
                                                                    ; Pvar offset_14394
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14395) (Pconst (8)%Z)
                                                                    ; Pvar t1_14403 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_14404.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_14392.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf2_14392
                                                                    ; Pvar offset_14394
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14395) (Pconst (8)%Z)
                                                                    ; Pvar t2_14404 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_14405.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14397)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_14393.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf3_14393
                                                                    ; Pvar offset_14394
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14395) (Pconst (8)%Z)
                                                                    ; Pvar t3_14405 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_14394.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14394) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14395) (Pconst (8)%Z))))) ]
                              [::]) ].

Definition fd_ABUFLEN____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____dumpstate_avx2x4;
    f_params := args_ABUFLEN____dumpstate_avx2x4;
    f_body := body_ABUFLEN____dumpstate_avx2x4;
    f_tyout := tyout_ABUFLEN____dumpstate_avx2x4;
    f_res := res_ABUFLEN____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
