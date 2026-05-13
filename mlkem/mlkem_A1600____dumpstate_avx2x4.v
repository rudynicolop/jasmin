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

(* A1600____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_14772 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14772).
Definition buf1_14773 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14773).
Definition buf2_14774 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14774).
Definition buf3_14775 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14775).
Definition offset_14776 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14776).
Definition _LEN_14777 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14777).
Definition st_14778 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14778).
Definition i_14779 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14779).
Definition x0_14780 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14780).
Definition x1_14781 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14781).
Definition x2_14782 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14782).
Definition x3_14783 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14783).
Definition t0_14784 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14784).
Definition t1_14785 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14785).
Definition t2_14786 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14786).
Definition t3_14787 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14787).

(* Signature *)
Definition tyin_A1600____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A1600____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_14772.(gv)
    ; buf1_14773.(gv)
    ; buf2_14774.(gv)
    ; buf3_14775.(gv)
    ; offset_14776.(gv)
    ; _LEN_14777.(gv)
    ; st_14778.(gv) ].
Definition tyout_A1600____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1600; aarr U8 1600; aarr U8 1600; aarr U8 1600; aword U64 ].
Definition res_A1600____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_14772.(gv)
    ; buf1_14773.(gv)
    ; buf2_14774.(gv)
    ; buf3_14775.(gv)
    ; offset_14776.(gv) ].

(* Body *)
Definition body_A1600____dumpstate_avx2x4 : cmd :=
  [:: cassgn (Lvar i_14779.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14779) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14777) (Pconst (32)%Z)))))
        [:: cassgn (Lvar x0_14780.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x1_14781.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x2_14782.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x3_14783.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar i_14779.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14779) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; ccall [:: Lvar x0_14780.(gv)
                    ; Lvar x1_14781.(gv)
                    ; Lvar x2_14782.(gv)
                    ; Lvar x3_14783.(gv) ] __4u64x4_u256x4 [:: Pvar x0_14780
                                                             ; Pvar x1_14781
                                                             ; Pvar x2_14782
                                                             ; Pvar x3_14783 ]
          ; cassgn (Laset Unaligned AAdirect U256 buf0_14772.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14776))) (aword U256) (Pvar x0_14780)
          ; cassgn (Laset Unaligned AAdirect U256 buf1_14773.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14776))) (aword U256) (Pvar x1_14781)
          ; cassgn (Laset Unaligned AAdirect U256 buf2_14774.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14776))) (aword U256) (Pvar x2_14782)
          ; cassgn (Laset Unaligned AAdirect U256 buf3_14775.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14776))) (aword U256) (Pvar x3_14783)
          ; cassgn (Lvar offset_14776.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14776) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14779) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14777) (Pconst (8)%Z)))))
        [:: cassgn (Lvar t0_14784.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf0_14772.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14776))) (aword U64) (Pvar t0_14784)
          ; cassgn (Lvar t1_14785.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf1_14773.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14776))) (aword U64) (Pvar t1_14785)
          ; cassgn (Lvar t2_14786.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf2_14774.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14776))) (aword U64) (Pvar t2_14786)
          ; cassgn (Lvar t3_14787.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf3_14775.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14776))) (aword U64) (Pvar t3_14787)
          ; cassgn (Lvar i_14779.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14779) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar offset_14776.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14776) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14777) (Pconst (8)%Z)))
        [:: cassgn (Lvar t0_14784.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf0_14772.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1600____a_ilen_write_upto8 [:: Pvar buf0_14772
                                                                    ; Pvar offset_14776
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14777) (Pconst (8)%Z)
                                                                    ; Pvar t0_14784 ]
          ; cassgn (Lvar t1_14785.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf1_14773.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1600____a_ilen_write_upto8 [:: Pvar buf1_14773
                                                                    ; Pvar offset_14776
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14777) (Pconst (8)%Z)
                                                                    ; Pvar t1_14785 ]
          ; cassgn (Lvar t2_14786.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf2_14774.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1600____a_ilen_write_upto8 [:: Pvar buf2_14774
                                                                    ; Pvar offset_14776
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14777) (Pconst (8)%Z)
                                                                    ; Pvar t2_14786 ]
          ; cassgn (Lvar t3_14787.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_14778 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_14779)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf3_14775.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1600____a_ilen_write_upto8 [:: Pvar buf3_14775
                                                                    ; Pvar offset_14776
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14777) (Pconst (8)%Z)
                                                                    ; Pvar t3_14787 ]
          ; cassgn (Lvar offset_14776.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14776) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14777) (Pconst (8)%Z)))) ]
        [::] ].

Definition fd_A1600____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____dumpstate_avx2x4;
    f_params := args_A1600____dumpstate_avx2x4;
    f_body := body_A1600____dumpstate_avx2x4;
    f_tyout := tyout_A1600____dumpstate_avx2x4;
    f_res := res_A1600____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
