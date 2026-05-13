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

(* A1568____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_15536 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15536).
Definition buf1_15537 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15537).
Definition buf2_15538 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15538).
Definition buf3_15539 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15539).
Definition offset_15540 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15540).
Definition _LEN_15541 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15541).
Definition st_15542 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15542).
Definition i_15543 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15543).
Definition x0_15544 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15544).
Definition x1_15545 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15545).
Definition x2_15546 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15546).
Definition x3_15547 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15547).
Definition t0_15548 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15548).
Definition t1_15549 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15549).
Definition t2_15550 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15550).
Definition t3_15551 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15551).

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
  [:: buf0_15536.(gv)
    ; buf1_15537.(gv)
    ; buf2_15538.(gv)
    ; buf3_15539.(gv)
    ; offset_15540.(gv)
    ; _LEN_15541.(gv)
    ; st_15542.(gv) ].
Definition tyout_A1568____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1568; aarr U8 1568; aarr U8 1568; aarr U8 1568; aword U64 ].
Definition res_A1568____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_15536.(gv)
    ; buf1_15537.(gv)
    ; buf2_15538.(gv)
    ; buf3_15539.(gv)
    ; offset_15540.(gv) ].

(* Body *)
Definition body_A1568____dumpstate_avx2x4 : cmd :=
  [:: cassgn (Lvar i_15543.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15543) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15541) (Pconst (32)%Z)))))
        [:: cassgn (Lvar x0_15544.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x1_15545.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x2_15546.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x3_15547.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar i_15543.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15543) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; ccall [:: Lvar x0_15544.(gv)
                    ; Lvar x1_15545.(gv)
                    ; Lvar x2_15546.(gv)
                    ; Lvar x3_15547.(gv) ] __4u64x4_u256x4 [:: Pvar x0_15544
                                                             ; Pvar x1_15545
                                                             ; Pvar x2_15546
                                                             ; Pvar x3_15547 ]
          ; cassgn (Laset Unaligned AAdirect U256 buf0_15536.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15540))) (aword U256) (Pvar x0_15544)
          ; cassgn (Laset Unaligned AAdirect U256 buf1_15537.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15540))) (aword U256) (Pvar x1_15545)
          ; cassgn (Laset Unaligned AAdirect U256 buf2_15538.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15540))) (aword U256) (Pvar x2_15546)
          ; cassgn (Laset Unaligned AAdirect U256 buf3_15539.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15540))) (aword U256) (Pvar x3_15547)
          ; cassgn (Lvar offset_15540.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15540) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15543) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15541) (Pconst (8)%Z)))))
        [:: cassgn (Lvar t0_15548.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf0_15536.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15540))) (aword U64) (Pvar t0_15548)
          ; cassgn (Lvar t1_15549.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf1_15537.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15540))) (aword U64) (Pvar t1_15549)
          ; cassgn (Lvar t2_15550.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf2_15538.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15540))) (aword U64) (Pvar t2_15550)
          ; cassgn (Lvar t3_15551.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf3_15539.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15540))) (aword U64) (Pvar t3_15551)
          ; cassgn (Lvar i_15543.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15543) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar offset_15540.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15540) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15541) (Pconst (8)%Z)))
        [:: cassgn (Lvar t0_15548.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf0_15536.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1568____a_ilen_write_upto8 [:: Pvar buf0_15536
                                                                    ; Pvar offset_15540
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15541) (Pconst (8)%Z)
                                                                    ; Pvar t0_15548 ]
          ; cassgn (Lvar t1_15549.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf1_15537.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1568____a_ilen_write_upto8 [:: Pvar buf1_15537
                                                                    ; Pvar offset_15540
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15541) (Pconst (8)%Z)
                                                                    ; Pvar t1_15549 ]
          ; cassgn (Lvar t2_15550.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf2_15538.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1568____a_ilen_write_upto8 [:: Pvar buf2_15538
                                                                    ; Pvar offset_15540
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15541) (Pconst (8)%Z)
                                                                    ; Pvar t2_15550 ]
          ; cassgn (Lvar t3_15551.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15542 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15543)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf3_15539.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1568____a_ilen_write_upto8 [:: Pvar buf3_15539
                                                                    ; Pvar offset_15540
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15541) (Pconst (8)%Z)
                                                                    ; Pvar t3_15551 ]
          ; cassgn (Lvar offset_15540.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15540) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15541) (Pconst (8)%Z)))) ]
        [::] ].

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
