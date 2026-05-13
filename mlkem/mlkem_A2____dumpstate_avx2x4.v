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

(* A2____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_17693 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17693).
Definition buf1_17694 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17694).
Definition buf2_17695 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17695).
Definition buf3_17696 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17696).
Definition offset_17697 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17697).
Definition _LEN_17698 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17698).
Definition st_17699 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17699).
Definition i_17700 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17700).
Definition x0_17701 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17701).
Definition x1_17702 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17702).
Definition x2_17703 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17703).
Definition x3_17704 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17704).
Definition t0_17705 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17705).
Definition t1_17706 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17706).
Definition t2_17707 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17707).
Definition t3_17708 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17708).

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
  [:: buf0_17693.(gv)
    ; buf1_17694.(gv)
    ; buf2_17695.(gv)
    ; buf3_17696.(gv)
    ; offset_17697.(gv)
    ; _LEN_17698.(gv)
    ; st_17699.(gv) ].
Definition tyout_A2____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 2; aarr U8 2; aarr U8 2; aarr U8 2; aword U64 ].
Definition res_A2____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_17693.(gv)
    ; buf1_17694.(gv)
    ; buf2_17695.(gv)
    ; buf3_17696.(gv)
    ; offset_17697.(gv) ].

(* Body *)
Definition body_A2____dumpstate_avx2x4 : cmd :=
  [:: cassgn (Lvar i_17700.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17700) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17698) (Pconst (32)%Z)))))
        [:: cassgn (Lvar x0_17701.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x1_17702.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x2_17703.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x3_17704.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar i_17700.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17700) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; ccall [:: Lvar x0_17701.(gv)
                    ; Lvar x1_17702.(gv)
                    ; Lvar x2_17703.(gv)
                    ; Lvar x3_17704.(gv) ] __4u64x4_u256x4 [:: Pvar x0_17701
                                                             ; Pvar x1_17702
                                                             ; Pvar x2_17703
                                                             ; Pvar x3_17704 ]
          ; cassgn (Laset Unaligned AAdirect U256 buf0_17693.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17697))) (aword U256) (Pvar x0_17701)
          ; cassgn (Laset Unaligned AAdirect U256 buf1_17694.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17697))) (aword U256) (Pvar x1_17702)
          ; cassgn (Laset Unaligned AAdirect U256 buf2_17695.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17697))) (aword U256) (Pvar x2_17703)
          ; cassgn (Laset Unaligned AAdirect U256 buf3_17696.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17697))) (aword U256) (Pvar x3_17704)
          ; cassgn (Lvar offset_17697.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17697) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17700) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17698) (Pconst (8)%Z)))))
        [:: cassgn (Lvar t0_17705.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf0_17693.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17697))) (aword U64) (Pvar t0_17705)
          ; cassgn (Lvar t1_17706.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf1_17694.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17697))) (aword U64) (Pvar t1_17706)
          ; cassgn (Lvar t2_17707.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf2_17695.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17697))) (aword U64) (Pvar t2_17707)
          ; cassgn (Lvar t3_17708.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf3_17696.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17697))) (aword U64) (Pvar t3_17708)
          ; cassgn (Lvar i_17700.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17700) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar offset_17697.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17697) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17698) (Pconst (8)%Z)))
        [:: cassgn (Lvar t0_17705.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf0_17693.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A2____a_ilen_write_upto8 [:: Pvar buf0_17693
                                                                    ; Pvar offset_17697
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17698) (Pconst (8)%Z)
                                                                    ; Pvar t0_17705 ]
          ; cassgn (Lvar t1_17706.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf1_17694.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A2____a_ilen_write_upto8 [:: Pvar buf1_17694
                                                                    ; Pvar offset_17697
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17698) (Pconst (8)%Z)
                                                                    ; Pvar t1_17706 ]
          ; cassgn (Lvar t2_17707.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf2_17695.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A2____a_ilen_write_upto8 [:: Pvar buf2_17695
                                                                    ; Pvar offset_17697
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17698) (Pconst (8)%Z)
                                                                    ; Pvar t2_17707 ]
          ; cassgn (Lvar t3_17708.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_17699 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_17700)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf3_17696.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A2____a_ilen_write_upto8 [:: Pvar buf3_17696
                                                                    ; Pvar offset_17697
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17698) (Pconst (8)%Z)
                                                                    ; Pvar t3_17708 ]
          ; cassgn (Lvar offset_17697.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17697) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17698) (Pconst (8)%Z)))) ]
        [::] ].

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
