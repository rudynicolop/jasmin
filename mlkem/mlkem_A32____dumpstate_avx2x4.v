From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* A32____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_17311 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17311).
Definition buf1_17312 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17312).
Definition buf2_17313 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17313).
Definition buf3_17314 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17314).
Definition offset_17315 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17315).
Definition _LEN_17316 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17316).
Definition st_17317 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17317).
Definition i_17318 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17318).
Definition x0_17319 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17319).
Definition x1_17320 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17320).
Definition x2_17321 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17321).
Definition x3_17322 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17322).
Definition t0_17323 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17323).
Definition t1_17324 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17324).
Definition t2_17325 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17325).
Definition t3_17326 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17326).

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
  [:: buf0_17311.(gv)
    ; buf1_17312.(gv)
    ; buf2_17313.(gv)
    ; buf3_17314.(gv)
    ; offset_17315.(gv)
    ; _LEN_17316.(gv)
    ; st_17317.(gv) ].
Definition tyout_A32____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 32; aarr U8 32; aarr U8 32; aarr U8 32; aword U64 ].
Definition res_A32____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_17311.(gv)
    ; buf1_17312.(gv)
    ; buf2_17313.(gv)
    ; buf3_17314.(gv)
    ; offset_17315.(gv) ].

(* Body *)
Definition body_A32____dumpstate_avx2x4 : cmd :=
  [:: cassgn (Lvar i_17318.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17318) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17316) (Pconst (32)%Z)))))
        [:: cassgn (Lvar x0_17319.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x1_17320.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x2_17321.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x3_17322.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar i_17318.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17318) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; ccall [:: Lvar x0_17319.(gv)
                    ; Lvar x1_17320.(gv)
                    ; Lvar x2_17321.(gv)
                    ; Lvar x3_17322.(gv) ] __4u64x4_u256x4 [:: Pvar x0_17319
                                                             ; Pvar x1_17320
                                                             ; Pvar x2_17321
                                                             ; Pvar x3_17322 ]
          ; cassgn (Laset Unaligned AAdirect U256 buf0_17311.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17315))) (aword U256) (Pvar x0_17319)
          ; cassgn (Laset Unaligned AAdirect U256 buf1_17312.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17315))) (aword U256) (Pvar x1_17320)
          ; cassgn (Laset Unaligned AAdirect U256 buf2_17313.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17315))) (aword U256) (Pvar x2_17321)
          ; cassgn (Laset Unaligned AAdirect U256 buf3_17314.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17315))) (aword U256) (Pvar x3_17322)
          ; cassgn (Lvar offset_17315.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17315) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17318) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17316) (Pconst (8)%Z)))))
        [:: cassgn (Lvar t0_17323.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf0_17311.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17315))) (aword U64) (Pvar t0_17323)
          ; cassgn (Lvar t1_17324.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf1_17312.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17315))) (aword U64) (Pvar t1_17324)
          ; cassgn (Lvar t2_17325.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf2_17313.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17315))) (aword U64) (Pvar t2_17325)
          ; cassgn (Lvar t3_17326.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf3_17314.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17315))) (aword U64) (Pvar t3_17326)
          ; cassgn (Lvar i_17318.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17318) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar offset_17315.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17315) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17316) (Pconst (8)%Z)))
        [:: cassgn (Lvar t0_17323.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf0_17311.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A32____a_ilen_write_upto8 [:: Pvar buf0_17311
                                                                    ; Pvar offset_17315
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17316) (Pconst (8)%Z)
                                                                    ; Pvar t0_17323 ]
          ; cassgn (Lvar t1_17324.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf1_17312.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A32____a_ilen_write_upto8 [:: Pvar buf1_17312
                                                                    ; Pvar offset_17315
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17316) (Pconst (8)%Z)
                                                                    ; Pvar t1_17324 ]
          ; cassgn (Lvar t2_17325.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf2_17313.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A32____a_ilen_write_upto8 [:: Pvar buf2_17313
                                                                    ; Pvar offset_17315
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17316) (Pconst (8)%Z)
                                                                    ; Pvar t2_17325 ]
          ; cassgn (Lvar t3_17326.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17317 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17318)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf3_17314.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A32____a_ilen_write_upto8 [:: Pvar buf3_17314
                                                                    ; Pvar offset_17315
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17316) (Pconst (8)%Z)
                                                                    ; Pvar t3_17326 ]
          ; cassgn (Lvar offset_17315.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17315) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17316) (Pconst (8)%Z)))) ]
        [::] ].

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
