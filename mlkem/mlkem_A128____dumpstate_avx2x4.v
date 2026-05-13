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

(* A128____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_16300 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16300).
Definition buf1_16301 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16301).
Definition buf2_16302 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16302).
Definition buf3_16303 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16303).
Definition offset_16304 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16304).
Definition _LEN_16305 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16305).
Definition st_16306 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 16306).
Definition i_16307 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16307).
Definition x0_16308 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16308).
Definition x1_16309 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16309).
Definition x2_16310 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16310).
Definition x3_16311 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16311).
Definition t0_16312 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16312).
Definition t1_16313 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16313).
Definition t2_16314 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16314).
Definition t3_16315 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16315).

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
  [:: buf0_16300.(gv)
    ; buf1_16301.(gv)
    ; buf2_16302.(gv)
    ; buf3_16303.(gv)
    ; offset_16304.(gv)
    ; _LEN_16305.(gv)
    ; st_16306.(gv) ].
Definition tyout_A128____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 128; aarr U8 128; aarr U8 128; aarr U8 128; aword U64 ].
Definition res_A128____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_16300.(gv)
    ; buf1_16301.(gv)
    ; buf2_16302.(gv)
    ; buf3_16303.(gv)
    ; offset_16304.(gv) ].

(* Body *)
Definition body_A128____dumpstate_avx2x4 : cmd :=
  [:: cassgn (Lvar i_16307.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16307) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16305) (Pconst (32)%Z)))))
        [:: cassgn (Lvar x0_16308.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x1_16309.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x2_16310.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x3_16311.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar i_16307.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16307) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; ccall [:: Lvar x0_16308.(gv)
                    ; Lvar x1_16309.(gv)
                    ; Lvar x2_16310.(gv)
                    ; Lvar x3_16311.(gv) ] __4u64x4_u256x4 [:: Pvar x0_16308
                                                             ; Pvar x1_16309
                                                             ; Pvar x2_16310
                                                             ; Pvar x3_16311 ]
          ; cassgn (Laset Unaligned AAdirect U256 buf0_16300.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16304))) (aword U256) (Pvar x0_16308)
          ; cassgn (Laset Unaligned AAdirect U256 buf1_16301.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16304))) (aword U256) (Pvar x1_16309)
          ; cassgn (Laset Unaligned AAdirect U256 buf2_16302.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16304))) (aword U256) (Pvar x2_16310)
          ; cassgn (Laset Unaligned AAdirect U256 buf3_16303.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16304))) (aword U256) (Pvar x3_16311)
          ; cassgn (Lvar offset_16304.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16304) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16307) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16305) (Pconst (8)%Z)))))
        [:: cassgn (Lvar t0_16312.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf0_16300.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16304))) (aword U64) (Pvar t0_16312)
          ; cassgn (Lvar t1_16313.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf1_16301.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16304))) (aword U64) (Pvar t1_16313)
          ; cassgn (Lvar t2_16314.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf2_16302.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16304))) (aword U64) (Pvar t2_16314)
          ; cassgn (Lvar t3_16315.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf3_16303.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16304))) (aword U64) (Pvar t3_16315)
          ; cassgn (Lvar i_16307.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16307) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar offset_16304.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16304) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16305) (Pconst (8)%Z)))
        [:: cassgn (Lvar t0_16312.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf0_16300.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A128____a_ilen_write_upto8 [:: Pvar buf0_16300
                                                                    ; Pvar offset_16304
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16305) (Pconst (8)%Z)
                                                                    ; Pvar t0_16312 ]
          ; cassgn (Lvar t1_16313.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf1_16301.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A128____a_ilen_write_upto8 [:: Pvar buf1_16301
                                                                    ; Pvar offset_16304
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16305) (Pconst (8)%Z)
                                                                    ; Pvar t1_16313 ]
          ; cassgn (Lvar t2_16314.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf2_16302.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A128____a_ilen_write_upto8 [:: Pvar buf2_16302
                                                                    ; Pvar offset_16304
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16305) (Pconst (8)%Z)
                                                                    ; Pvar t2_16314 ]
          ; cassgn (Lvar t3_16315.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_16306 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16307)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf3_16303.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A128____a_ilen_write_upto8 [:: Pvar buf3_16303
                                                                    ; Pvar offset_16304
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16305) (Pconst (8)%Z)
                                                                    ; Pvar t3_16315 ]
          ; cassgn (Lvar offset_16304.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16304) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16305) (Pconst (8)%Z)))) ]
        [::] ].

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
