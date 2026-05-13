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

(* A1____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_18075 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18075).
Definition buf1_18076 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18076).
Definition buf2_18077 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18077).
Definition buf3_18078 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18078).
Definition offset_18079 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18079).
Definition _LEN_18080 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18080).
Definition st_18081 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18081).
Definition i_18082 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18082).
Definition x0_18083 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18083).
Definition x1_18084 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18084).
Definition x2_18085 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18085).
Definition x3_18086 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18086).
Definition t0_18087 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18087).
Definition t1_18088 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18088).
Definition t2_18089 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18089).
Definition t3_18090 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18090).

(* Signature *)
Definition tyin_A1____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1
    ; aarr U8 1
    ; aarr U8 1
    ; aarr U8 1
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A1____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_18075.(gv)
    ; buf1_18076.(gv)
    ; buf2_18077.(gv)
    ; buf3_18078.(gv)
    ; offset_18079.(gv)
    ; _LEN_18080.(gv)
    ; st_18081.(gv) ].
Definition tyout_A1____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1; aarr U8 1; aarr U8 1; aarr U8 1; aword U64 ].
Definition res_A1____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_18075.(gv)
    ; buf1_18076.(gv)
    ; buf2_18077.(gv)
    ; buf3_18078.(gv)
    ; offset_18079.(gv) ].

(* Body *)
Definition body_A1____dumpstate_avx2x4 : cmd :=
  [:: cassgn (Lvar i_18082.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18082) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18080) (Pconst (32)%Z)))))
        [:: cassgn (Lvar x0_18083.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x1_18084.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x2_18085.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x3_18086.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar i_18082.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18082) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; ccall [:: Lvar x0_18083.(gv)
                    ; Lvar x1_18084.(gv)
                    ; Lvar x2_18085.(gv)
                    ; Lvar x3_18086.(gv) ] __4u64x4_u256x4 [:: Pvar x0_18083
                                                             ; Pvar x1_18084
                                                             ; Pvar x2_18085
                                                             ; Pvar x3_18086 ]
          ; cassgn (Laset Unaligned AAdirect U256 buf0_18075.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18079))) (aword U256) (Pvar x0_18083)
          ; cassgn (Laset Unaligned AAdirect U256 buf1_18076.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18079))) (aword U256) (Pvar x1_18084)
          ; cassgn (Laset Unaligned AAdirect U256 buf2_18077.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18079))) (aword U256) (Pvar x2_18085)
          ; cassgn (Laset Unaligned AAdirect U256 buf3_18078.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18079))) (aword U256) (Pvar x3_18086)
          ; cassgn (Lvar offset_18079.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18079) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18082) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18080) (Pconst (8)%Z)))))
        [:: cassgn (Lvar t0_18087.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf0_18075.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18079))) (aword U64) (Pvar t0_18087)
          ; cassgn (Lvar t1_18088.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf1_18076.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18079))) (aword U64) (Pvar t1_18088)
          ; cassgn (Lvar t2_18089.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf2_18077.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18079))) (aword U64) (Pvar t2_18089)
          ; cassgn (Lvar t3_18090.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf3_18078.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18079))) (aword U64) (Pvar t3_18090)
          ; cassgn (Lvar i_18082.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18082) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar offset_18079.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18079) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18080) (Pconst (8)%Z)))
        [:: cassgn (Lvar t0_18087.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf0_18075.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1____a_ilen_write_upto8 [:: Pvar buf0_18075
                                                                    ; Pvar offset_18079
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18080) (Pconst (8)%Z)
                                                                    ; Pvar t0_18087 ]
          ; cassgn (Lvar t1_18088.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf1_18076.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1____a_ilen_write_upto8 [:: Pvar buf1_18076
                                                                    ; Pvar offset_18079
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18080) (Pconst (8)%Z)
                                                                    ; Pvar t1_18088 ]
          ; cassgn (Lvar t2_18089.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf2_18077.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1____a_ilen_write_upto8 [:: Pvar buf2_18077
                                                                    ; Pvar offset_18079
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18080) (Pconst (8)%Z)
                                                                    ; Pvar t2_18089 ]
          ; cassgn (Lvar t3_18090.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18081 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18082)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf3_18078.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1____a_ilen_write_upto8 [:: Pvar buf3_18078
                                                                    ; Pvar offset_18079
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18080) (Pconst (8)%Z)
                                                                    ; Pvar t3_18090 ]
          ; cassgn (Lvar offset_18079.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18079) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18080) (Pconst (8)%Z)))) ]
        [::] ].

Definition fd_A1____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____dumpstate_avx2x4;
    f_params := args_A1____dumpstate_avx2x4;
    f_body := body_A1____dumpstate_avx2x4;
    f_tyout := tyout_A1____dumpstate_avx2x4;
    f_res := res_A1____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
