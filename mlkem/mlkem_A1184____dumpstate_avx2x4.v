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

(* A1184____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_15918 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15918).
Definition buf1_15919 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15919).
Definition buf2_15920 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15920).
Definition buf3_15921 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15921).
Definition offset_15922 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15922).
Definition _LEN_15923 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15923).
Definition st_15924 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15924).
Definition i_15925 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15925).
Definition x0_15926 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15926).
Definition x1_15927 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15927).
Definition x2_15928 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15928).
Definition x3_15929 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15929).
Definition t0_15930 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15930).
Definition t1_15931 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15931).
Definition t2_15932 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15932).
Definition t3_15933 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15933).

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
  [:: buf0_15918.(gv)
    ; buf1_15919.(gv)
    ; buf2_15920.(gv)
    ; buf3_15921.(gv)
    ; offset_15922.(gv)
    ; _LEN_15923.(gv)
    ; st_15924.(gv) ].
Definition tyout_A1184____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1184; aarr U8 1184; aarr U8 1184; aarr U8 1184; aword U64 ].
Definition res_A1184____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_15918.(gv)
    ; buf1_15919.(gv)
    ; buf2_15920.(gv)
    ; buf3_15921.(gv)
    ; offset_15922.(gv) ].

(* Body *)
Definition body_A1184____dumpstate_avx2x4 : cmd :=
  [:: cassgn (Lvar i_15925.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15925) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15923) (Pconst (32)%Z)))))
        [:: cassgn (Lvar x0_15926.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x1_15927.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x2_15928.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x3_15929.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar i_15925.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15925) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; ccall [:: Lvar x0_15926.(gv)
                    ; Lvar x1_15927.(gv)
                    ; Lvar x2_15928.(gv)
                    ; Lvar x3_15929.(gv) ] __4u64x4_u256x4 [:: Pvar x0_15926
                                                             ; Pvar x1_15927
                                                             ; Pvar x2_15928
                                                             ; Pvar x3_15929 ]
          ; cassgn (Laset Unaligned AAdirect U256 buf0_15918.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15922))) (aword U256) (Pvar x0_15926)
          ; cassgn (Laset Unaligned AAdirect U256 buf1_15919.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15922))) (aword U256) (Pvar x1_15927)
          ; cassgn (Laset Unaligned AAdirect U256 buf2_15920.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15922))) (aword U256) (Pvar x2_15928)
          ; cassgn (Laset Unaligned AAdirect U256 buf3_15921.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15922))) (aword U256) (Pvar x3_15929)
          ; cassgn (Lvar offset_15922.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15922) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15925) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15923) (Pconst (8)%Z)))))
        [:: cassgn (Lvar t0_15930.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf0_15918.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15922))) (aword U64) (Pvar t0_15930)
          ; cassgn (Lvar t1_15931.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf1_15919.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15922))) (aword U64) (Pvar t1_15931)
          ; cassgn (Lvar t2_15932.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf2_15920.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15922))) (aword U64) (Pvar t2_15932)
          ; cassgn (Lvar t3_15933.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf3_15921.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15922))) (aword U64) (Pvar t3_15933)
          ; cassgn (Lvar i_15925.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15925) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar offset_15922.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15922) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15923) (Pconst (8)%Z)))
        [:: cassgn (Lvar t0_15930.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf0_15918.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1184____a_ilen_write_upto8 [:: Pvar buf0_15918
                                                                    ; Pvar offset_15922
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15923) (Pconst (8)%Z)
                                                                    ; Pvar t0_15930 ]
          ; cassgn (Lvar t1_15931.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf1_15919.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1184____a_ilen_write_upto8 [:: Pvar buf1_15919
                                                                    ; Pvar offset_15922
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15923) (Pconst (8)%Z)
                                                                    ; Pvar t1_15931 ]
          ; cassgn (Lvar t2_15932.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf2_15920.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1184____a_ilen_write_upto8 [:: Pvar buf2_15920
                                                                    ; Pvar offset_15922
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15923) (Pconst (8)%Z)
                                                                    ; Pvar t2_15932 ]
          ; cassgn (Lvar t3_15933.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15924 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15925)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf3_15921.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1184____a_ilen_write_upto8 [:: Pvar buf3_15921
                                                                    ; Pvar offset_15922
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15923) (Pconst (8)%Z)
                                                                    ; Pvar t3_15933 ]
          ; cassgn (Lvar offset_15922.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15922) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15923) (Pconst (8)%Z)))) ]
        [::] ].

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
